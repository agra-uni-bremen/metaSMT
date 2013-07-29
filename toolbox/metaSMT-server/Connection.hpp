#pragma once
#include "Solver.hpp"
#include <boost/asio/ip/tcp.hpp>
#include <boost/asio/streambuf.hpp>
#include <boost/shared_ptr.hpp>
#include <list>
#include <ctime>

class Connection {
public:
  typedef boost::shared_ptr<boost::asio::ip::tcp::socket> SocketPtr;
  typedef std::list<SolverProcess*> Solvers;

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

private:
  SocketPtr socket;
  boost::asio::streambuf buffer;
  Solvers solvers;
  bool timeoutEnabled;
  int timeoutThreshold;
  time_t startTime;
}; // Connection
