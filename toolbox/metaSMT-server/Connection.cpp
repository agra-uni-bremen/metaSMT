#include <metaSMT/support/default_visitation_unrolling_limit.hpp>
#include "Connection.hpp"
#include "create_solver.hpp"
#include <boost/lexical_cast.hpp>
#include <boost/algorithm/string/classification.hpp>
#include <boost/algorithm/string/predicate.hpp>
#include <boost/algorithm/string/split.hpp>
#include <boost/asio/read_until.hpp>
#include <boost/asio/write.hpp>
#include <sys/wait.h>

namespace mpl = boost::mpl;

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
    startTime = time(NULL);
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
            write( "Unable to parse optional timeout parameter" );
            continue;
          }
          std::cout << "Timeout after " << timeoutThreshold << " seconds" << std::endl;
        }

        if (solvers.empty()) {
          write( "Choose at least one solver" );
        } else {
          write( "OK" );
          return;
        }
      } else {
        write( "To many parameters" );
      }
    } else if ( metaSMT::isSolverAvailable(str) ) {
      solvers.push_back(new SolverProcess(str));
      write( "OK" );
    } else {
      write( "Unsupported solver or command" );
    }
  }
}

bool Connection::createSolverProcesses() {
  for (Solvers::iterator it = solvers.begin(), ie = solvers.end();
       it != ie; ++it) {
    SolverProcess *solver = *it;
    if ( !solver->initPipes() ) {
      write("Could not create pipe for IPC");
      return false;
    }
    pid_t pid = fork();
    if (pid == -1) {
      write("Could not fork new process");
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
  SolverProcess *solver = findFastestSolver();
  assert( solver && "solver must not be NULL" );
  std::string const result = solver->parent_read_command() + " ;; " + solver->solver_type;
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
      return "FAIL inconsistent solver behavior";
    }
  }
  return answers[0];
}

void Connection::processCommandsLoop() {
  std::string line;
  while ( true ) {
    checkTimeout();
    line = getLine();
    // std::cerr << "[SERVER] RECEIVED " << line << '\n';

    if ( line == "(exit)" ) {
      write("OK");
      return;
    }

    // forward command to solver backend
    for (Solvers::iterator it = solvers.begin(), ie = solvers.end();
         it != ie; ++it) {
      (*it)->parent_write_command(line);
    }

    // pass resultl of check-sat and get-value to the client
    if ( line == "(check-sat)" ) {
      write ( checkSat() );
      timeoutEnabled = false;
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
  if (timeoutEnabled && difftime(time(NULL), startTime) > timeoutThreshold) {
    write( "timeout" );
    throw std::runtime_error("Solver timeout");
  }
}
