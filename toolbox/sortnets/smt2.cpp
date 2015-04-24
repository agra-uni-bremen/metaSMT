#include <metaSMT/support/default_visitation_unrolling_limit.hpp>
#include "Main.hpp"

#include <metaSMT/API/Comment.hpp>
#include <metaSMT/DirectSolver_Context.hpp>
#include <metaSMT/backend/SMT2.hpp>

using namespace metaSMT;



int main(int argc, const char *argv[])
{
  Main<
      DirectSolver_Context < IgnoreComments < solver::SMT2 > >
    , DirectSolver_Context < IgnoreComments < solver::SMT2 > >
    > m(argc, argv);

  return m.run();
}
