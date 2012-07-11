

#include <metaSMT/support/disable_warnings.hpp>
#include <boost/python.hpp>
#include <metaSMT/support/enable_warnings.hpp>

#include <metaSMT/expression/default_visitation_unrolling_limit.hpp>
#include "solvers.hpp"
#include <metaSMT/expression/expression.hpp>

void export_expressions();

BOOST_PYTHON_MODULE( metasmt_python )
{

  export_expressions();
  export_solvers();

}
