#include <metaSMT/support/default_visitation_unrolling_limit.hpp>
#include <metaSMT/DirectSolver_Context.hpp>
#include <metaSMT/API/Stack.hpp>
#include <metaSMT/backend/MiniSAT.hpp>
#include <metaSMT/backend/SAT_Clause.hpp>
#include <metaSMT/API/Group.hpp>
#include <metaSMT/BitBlast.hpp>

typedef metaSMT::DirectSolver_Context<
  metaSMT::Group<
    metaSMT::BitBlast<
      metaSMT::SAT_Clause<
        metaSMT::Stack<metaSMT::solver::MiniSAT>
        >
      >
    >
  > ContextType;

#include "main.cpp"
