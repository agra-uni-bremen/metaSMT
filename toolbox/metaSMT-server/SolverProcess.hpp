#pragma once
#include <string>

class SolverProcess;

class SolverBase {
public:
  virtual void start() = 0;
  virtual ~SolverBase() {};

  static const std::string success;
  static const std::string unsupported;
  static const std::string error;

  static const std::string sat;
  static const std::string unsat;
  static const std::string unknown;
// protected:
  SolverProcess *sp;
}; // SolverBase

class SolverProcess {
public:
  SolverProcess(std::string const &solver_type);
  ~SolverProcess();

  int initPipes();

  std::string child_read_command();
  void child_write_command(std::string s);

  bool parent_read_command_available();
  std::string parent_read_command();
  void parent_write_command(std::string s);

  SolverBase *sb;
  std::string solver_type;
  pid_t pid;

public: // private:
  int fd_p2c[2];
  int fd_c2p[2];

  std::string p2c_read_command;

  std::string read_command(int fd);
  void write_command(int fd, std::string s);
}; // SolverProcess
