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
    timeoutThreshold(-1),
    preferredSolver(0) {
  std::string exit_reason = "requested by client";
  try {
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
  write( metaSMT::getAvailableSolversString() );

  while ( solvers.empty() ) {
    std::string str = getLine();
    str.erase(str.find_last_not_of(")") + 1);
    std::vector<std::string> tokens;
    boost::split(tokens, str, boost::algorithm::is_any_of(" "));

    if (tokens.size() >= 3 && tokens[0] == "(set-option" && tokens[1] == ":solver" ) {
      bool solversAvailable = true;
      for ( int n = 2; n < tokens.size(); ++n ) {
        std::cerr << tokens[n] << '\n';
        if ( !metaSMT::isSolverAvailable(tokens[n]) ) {
            solversAvailable = false;
        }
      }
      if (solversAvailable) {
        for ( int n = 2; n < tokens.size(); ++n ) {
            solvers.reserve( tokens.size() - 2 );
            solvers.push_back(new SolverProcess(tokens[n]));
        }
        preferredSolver = solvers.front();
        write( SolverBase::success );
      } else {
        write( SolverBase::unsupported + " not all solvers supported" );
      }
    } else {
      write( SolverBase::error + " set at least one solver" );
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
  int level = preferredSolver->num_answers;
  while ( true ) {
    checkTimeout();
    for (Solvers::iterator it = solvers.begin(), ie = solvers.end();
         it != ie; ++it) {
      if ((*it)->parent_read_command_available()) {
        if ((*it)->num_answers == level) {
          return *it;
        } else {
          //ignore answer
          (*it)->parent_read_command();
        }
      }
    }
    usleep(100);
  }
}

std::string Connection::checkSat() {
  gettimeofday(&checkSatStartTime, NULL);
  preferredSolver = findFastestSolver();
  assert( preferredSolver && "preferredSolver must not be NULL" );

  timeval currentTime;
  gettimeofday(&currentTime, NULL);
  long int ms = (currentTime.tv_sec - checkSatStartTime.tv_sec) * 1000;
  ms += (currentTime.tv_usec - checkSatStartTime.tv_usec) / 1000;

  std::stringstream ss;
  ss << std::fixed << std::setprecision(2) << ms / 1000.0;
  std::string const result = preferredSolver->parent_read_command() + " ;; " + preferredSolver->solver_type + " ;; " + ss.str();

  skipAnswers( preferredSolver->num_answers );

  return result;
}

void Connection::processCommandsLoop() {
  gettimeofday(&startTime, NULL);

  std::string line;
  while ( true ) {
    line = getLine();
    //std::cerr << "[SERVER] RECEIVED " << line << '\n';

    if ( line == "(exit)" ) {
      timeval currentTime;
      gettimeofday(&currentTime, NULL);
      long int ms = (currentTime.tv_sec - startTime.tv_sec) * 1000;
      ms += (currentTime.tv_usec - startTime.tv_usec) / 1000;

      std::stringstream ss;
      ss << std::fixed << std::setprecision(2) << ms / 1000.0;

      write( SolverBase::success + " ;; " + ss.str() );
      return;
    } else if ( boost::algorithm::starts_with(line, "(set-option :timeout") ) {
        std::string str = line;
        str.erase(str.find_last_not_of(")") + 1);
        std::vector<std::string> tokens;
        boost::split(tokens, str, boost::algorithm::is_any_of(" "));
        try {
            timeoutThreshold = boost::lexical_cast<unsigned>(tokens[2]);
            timeoutEnabled = true;
            write( SolverBase::success );
        } catch (boost::bad_lexical_cast) {
            write( SolverBase::error + " unable to parse timeout parameter" );
        }
        continue;
    }

    // forward command to solver backend
    for (Solvers::iterator it = solvers.begin(), ie = solvers.end();
         it != ie; ++it) {
      (*it)->parent_write_command(line);
    }

    // pass result of check-sat and get-value to the client
    if ( line == "(check-sat)" ) {
      std::cout << "(check-sat) called" << std::endl;
      std::string ret;
      try {
        ret = checkSat();
      } catch (std::runtime_error e) {
        ret = e.what();
      }
      timeoutEnabled = false;
      write( ret );
    } else {
      // print result and ignore potential results of other solvers
      write( preferredSolver->parent_read_command() );
      skipAnswers( preferredSolver->num_answers );
    }
  }
}

void Connection::skipAnswers(int level) {
  for ( int n = 0; n < solvers.size(); ++n ) {
    while ( solvers[n]->num_answers < level && solvers[n]->parent_read_command_available() ) {
      solvers[n]->parent_read_command();
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
  std::cout << '[' << getpid() << "] killing " << solver->solver_type << " (" << solver->pid << ')' << std::endl;
  kill(solver->pid, SIGTERM);
  int status;
  waitpid(solver->pid, &status, 0);
  std::cout << "killed " << solver->pid << std::endl;
  delete solver;
}

void Connection::checkTimeout() {
  if (timeoutEnabled) {
    timeval currentTime;
    gettimeofday(&currentTime, NULL);
    long int secs = currentTime.tv_sec - checkSatStartTime.tv_sec;

    if (secs >= timeoutThreshold) {
        throw std::runtime_error( SolverBase::unknown );
    }
  }
}
