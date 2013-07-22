#pragma once
#include "Solver.hpp"
#include <boost/asio/ip/tcp.hpp>
#include <boost/asio/streambuf.hpp>
#include <boost/shared_ptr.hpp>
#include <list>

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
  void write(std::string const &string);
  void terminateSolver(SolverProcess *solver);

  void setupSolverProcesses();
  bool initializeSolverBackends();
  SolverProcess *findFastestSolver();
  std::string getValue();
  std::string checkSat();
  void processCommandsLoop();

private:
  SocketPtr socket;
  boost::asio::streambuf buffer;
  Solvers solvers;
}; // Connection
