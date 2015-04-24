#include "Main.hpp"

#include <metaSMT/API/Comment.hpp>
#include <metaSMT/DirectSolver_Context.hpp>
#include <metaSMT/backend/SWORD_Backend.hpp>

using namespace metaSMT;

typedef DirectSolver_Context< IgnoreComments<solver::SWORD_Backend> > DirectSwordContext;


int main(int argc, const char *argv[])
{
  Main<DirectSwordContext, DirectSwordContext> m(argc, argv);

  return m.run();
}
