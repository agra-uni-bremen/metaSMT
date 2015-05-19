#include "Main.hpp"

#include <metaSMT/API/Comment.hpp>
#include <metaSMT/DirectSolver_Context.hpp>
#include <metaSMT/backend/STP.hpp>

using namespace metaSMT;

int main(int argc, const char *argv[])
{
  Main<
      DirectSolver_Context < IgnoreComments < solver::STP > >,
      DirectSolver_Context < IgnoreComments < solver::STP > >
    > m(argc, argv);

  return m.run();
}
