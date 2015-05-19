#include "Main.hpp"

#include <metaSMT/API/Comment.hpp>
#include <metaSMT/DirectSolver_Context.hpp>
#include <metaSMT/backend/Z3_Backend.hpp>

using namespace metaSMT;

typedef DirectSolver_Context< IgnoreComments<solver::Z3_Backend> > DirectZ3Context;


int main(int argc, const char *argv[])
{
  Main<DirectZ3Context, DirectZ3Context> m(argc, argv);

  return m.run();
}
