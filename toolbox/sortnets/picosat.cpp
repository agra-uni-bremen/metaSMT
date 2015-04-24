#include "Main.hpp"

#include <metaSMT/API/Comment.hpp>
#include <metaSMT/BitBlast.hpp>
#include <metaSMT/DirectSolver_Context.hpp>
#include <metaSMT/backend/MiniSAT.hpp>
#include <metaSMT/backend/PicoSAT.hpp>
#include <metaSMT/backend/SAT_Aiger.hpp>

using namespace metaSMT;



int main(int argc, const char *argv[])
{
  Main<
      DirectSolver_Context < IgnoreComments < BitBlast < SAT_Aiger < solver::PicoSAT > > > >
    , DirectSolver_Context < IgnoreComments < BitBlast < SAT_Aiger < solver::MiniSAT > > > >
    > m(argc, argv);

  return m.run();
}
