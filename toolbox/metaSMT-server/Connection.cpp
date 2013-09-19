#include <metaSMT/support/default_visitation_unrolling_limit.hpp>
#include "Connection.hpp"
#include "create_solver.hpp"
#include <boost/lexical_cast.hpp>
#include <boost/algorithm/string/classification.hpp>
#include <boost/algorithm/string/predicate.hpp>
#include <boost/algorithm/string/split.hpp>
#include <boost/asio/read_until.hpp>
#include <boost/asio/write.hpp>
#include <iomanip>
#include <sys/wait.h>

void Connection::new_connection(SocketPtr socket) {
  std::cout << "New connection" << std::endl;
  Connection c(socket);
}

Connection::Connection(SocketPtr socket)
  : socket(socket),
    timeoutEnabled(false),
    timeoutThreshold(-1) {
  std::string exit_reason = "requested by client";
  try {
    write( metaSMT::getAvailableSolversString() );
    setupSolvers();
    if ( !createSolverProcesses() ) {
      return;
    }
    processCommandsLoop();
  }
  catch (std::exception &e) {
    exit_reason = e.what();
  }

  std::cout << "Closing connection: " << exit_reason << std::endl;

  for (Solvers::iterator it = solvers.begin(), ie = solvers.end();
       it != ie; ++it) {
    terminateSolver(*it);
  }
  socket->close();
}

void Connection::setupSolvers() {
  // send solver information to client and wait for client response,
  // i.e., the selection of the solvers for solving the SMT instance.
  std::string str;
  while ( true ) {
    str = getLine();

    if (boost::algorithm::starts_with(str, "start")) {
      std::vector<std::string> split;
      boost::split(split, str, boost::algorithm::is_any_of(" "));

      if (split.size() <= 2u) {
        if (split.size() == 2u) {
          try {
            timeoutThreshold = boost::lexical_cast<unsigned>(split[1]);
            timeoutEnabled = true;
          } catch (boost::bad_lexical_cast) {
            write( SolverBase::error + " unable to parse optional timeout parameter" );
            continue;
          }
          std::cout << "Timeout after " << timeoutThreshold << " seconds" << std::endl;
        }

        if (solvers.empty()) {
          write( SolverBase::error + " choose at least one solver" );
        } else {
          write( SolverBase::success );
          return;
        }
      } else {
        write( SolverBase::error + " to many parameters" );
      }
    } else if ( metaSMT::isSolverAvailable(str) ) {
      solvers.push_back(new SolverProcess(str));
      write( SolverBase::success );
    } else {
      write( SolverBase::unsupported + " solver or command" );
    }
  }
}

bool Connection::createSolverProcesses() {
  for (Solvers::iterator it = solvers.begin(), ie = solvers.end();
       it != ie; ++it) {
    SolverProcess *solver = *it;
    if ( !solver->initPipes() ) {
      write(SolverBase::error + " could not create pipes for IPC");
      return false;
    }
    pid_t pid = fork();
    if (pid == -1) {
      write(SolverBase::error + " could not fork new process");
      return false;
    }
    else if (pid) {
      // parent process
      solver->pid = pid;
    }
    else {
      // child process
      solver->sb = create_solver( solver->solver_type );
      solver->sb->sp = solver;
      solver->sb->start();
      return false;
    }
  }
  return true;
}

SolverProcess *Connection::findFastestSolver() {
  while ( true ) {
    checkTimeout();
    for (Solvers::iterator it = solvers.begin(), ie = solvers.end();
         it != ie; ++it) {
      if ((*it)->parent_read_command_available()) {
        return *it;
      }
    }
    usleep(100);
  }
}

std::string Connection::checkSat() {
  gettimeofday(&checkSatStartTime, NULL);
  SolverProcess *solver = findFastestSolver();
  assert( solver && "solver must not be NULL" );

  timeval currentTime;
  gettimeofday(&currentTime, NULL);
  long int ms = (currentTime.tv_sec - checkSatStartTime.tv_sec) * 1000;
  ms += (currentTime.tv_usec - checkSatStartTime.tv_usec) / 1000;

  std::stringstream ss;
  ss << std::fixed << std::setprecision(2) << ms / 1000.0;
  std::string const result = solver->parent_read_command() + " ;; " + solver->solver_type + " ;; " + ss.str();
  // terminate all but the fastest solver
  for ( Solvers::iterator it = solvers.begin(), ie  = solvers.end();
        it != ie; ++it ) {
    if ( *it != solver ) {
      terminateSolver(*it);
    }
  }
  solvers.clear();
  solvers.push_back(solver);
  return result;
}


std::string Connection::getValue() {
  typedef std::vector<std::string> Answers;
  Answers answers(solvers.size());
  std::size_t n = 0;
  for ( Solvers::iterator it = solvers.begin(), ie = solvers.end();
        it != ie; ++it, ++n ) {
    answers[n] = (*it)->parent_read_command();
  }

  // return a FAIL if not all answers are the same, otherwise return
  // the consistent answer
  for (std::size_t n = 0; n < answers.size() -1; n++) {
    if (answers[n] != answers[n+1]) {
      return SolverBase::error + " inconsistent solver behavior";
    }
  }
  return answers[0];
}

void Connection::processCommandsLoop() {
  gettimeofday(&startTime, NULL);

  std::string line;
  while ( true ) {
    line = getLine();
    // std::cerr << "[SERVER] RECEIVED " << line << '\n';

    if ( line == "(exit)" ) {
      timeval currentTime;
      gettimeofday(&currentTime, NULL);
      long int ms = (currentTime.tv_sec - startTime.tv_sec) * 1000;
      ms += (currentTime.tv_usec - startTime.tv_usec) / 1000;

      std::stringstream ss;
      ss << std::fixed << std::setprecision(2) << ms / 1000.0;

      write( SolverBase::success + " ;; " + ss.str() );
      return;
    }

    // forward command to solver backend
    for (Solvers::iterator it = solvers.begin(), ie = solvers.end();
         it != ie; ++it) {
      (*it)->parent_write_command(line);
    }

    // pass result of check-sat and get-value to the client
    if ( line == "(check-sat)" ) {
      write ( checkSat() );
    }
    else if ( boost::algorithm::starts_with(line, "(get-value") ) {
      write( getValue() );
    }
    else {
      // otherwise, ignore result from solver backend
      for (Solvers::iterator it = solvers.begin(), ie = solvers.end();
           it != ie; ++it) {
        std::string const s = (*it)->parent_read_command();
        write( s );
      }
    }
  }
}

std::string Connection::getLine() {
  boost::system::error_code error;
  std::size_t len = read_until(*socket, buffer, '\n', error);
  if (error) throw boost::system::system_error(error);
  std::string s;
  std::istream is(&buffer);
  std::getline(is, s);
  s.erase(s.find_last_not_of(" \n\r\t") + 1);
  return s;
}

void Connection::write(std::string s) {
  s += '\n';
  boost::asio::write(*socket, boost::asio::buffer(s, s.size()));
}

void Connection::terminateSolver(SolverProcess *solver) {
  kill(solver->pid, SIGTERM);
  int status;
  waitpid(solver->pid, &status, 0);
  delete solver;
}

void Connection::checkTimeout() {
  if (timeoutEnabled) {
    timeval currentTime;
    gettimeofday(&currentTime, NULL);
    long int secs = currentTime.tv_sec - checkSatStartTime.tv_sec;

    if (secs > timeoutThreshold) {
        throw std::runtime_error( SolverBase::unknown );
    }
  }
}
