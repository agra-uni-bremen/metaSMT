#pragma once
#include "Solver.hpp"
#include <boost/asio/ip/tcp.hpp>
#include <boost/asio/streambuf.hpp>
#include <boost/shared_ptr.hpp>
#include <vector>
#include <sys/time.h>

class Connection {
public:
  typedef boost::shared_ptr<boost::asio::ip::tcp::socket> SocketPtr;
  typedef std::vector<SolverProcess*> Solvers;

public:
  static void new_connection(SocketPtr socket);

public:
  Connection(SocketPtr socket);

private:
  std::string getLine();
  void write(std::string string);
  void terminateSolver(SolverProcess *solver);

  void setupSolvers();
  bool createSolverProcesses();
  SolverProcess *findFastestSolver();
  std::string getValue();
  std::string checkSat();
  void processCommandsLoop();
  void checkTimeout();
  void skipAnswers(int level);

private:
  SocketPtr socket;
  boost::asio::streambuf buffer;
  Solvers solvers;
  SolverProcess* preferredSolver;
  bool timeoutEnabled;
  int timeoutThreshold;
  timeval startTime;
  timeval checkSatStartTime;
}; // Connection
