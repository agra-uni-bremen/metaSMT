#define BOOST_TEST_MODULE test_sat
#include <boost/test/unit_test.hpp>

//internal includes
#include <metaSMT/frontend/SAT.hpp>
#include <metaSMT/transform/satClause.hpp>
#include <metaSMT/backend/MiniSAT.hpp>

//external includes
#include <boost/array.hpp>
#include <boost/proto/debug.hpp>
#include <boost/proto/fusion.hpp>
#include <boost/fusion/include/io.hpp>

using namespace metaSMT;

class sat_Fixture {
  protected:
};

using SAT::variable;
using SAT::new_variable;
using boost::proto::display_expr;

//template< typename Context, typename Expr >
//typename boost::result_of< transform::satClause( Expr )>::type
//evaluate ( Context const & , Expr const & ) {
//  return boost::result_of< transform::satClause( Expr )>::type::value;
//}

BOOST_FIXTURE_TEST_SUITE(sat_t, sat_Fixture )

BOOST_AUTO_TEST_CASE( syntax )
{
  SAT::variable x=new_variable(), y=new_variable(), z=new_variable();

  display_expr( 
    x + !y + !~z
  );

  std::cout << transform::satClauseArity() (
      x+!y+!~z
 ) << std::endl;


  display_expr(
      x+ y + (-z)
  );

  std::cout << transform::satClause() (
      x + y + -(-(-z))
 ) << std::endl;

}

BOOST_AUTO_TEST_SUITE_END() //QF_BV

//  vim: ft=cpp:ts=2:sw=2:expandtab
