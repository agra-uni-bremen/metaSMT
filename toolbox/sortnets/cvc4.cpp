#include "Main.hpp"

#include <metaSMT/API/Comment.hpp>
#include <metaSMT/DirectSolver_Context.hpp>
#include <metaSMT/backend/CVC4.hpp>

using namespace metaSMT;

int main(int argc, const char *argv[])
{
  Main<
      DirectSolver_Context < IgnoreComments < solver::CVC4 > >
    , DirectSolver_Context < IgnoreComments < solver::CVC4 > >
    > m(argc, argv);

  return m.run();
}
