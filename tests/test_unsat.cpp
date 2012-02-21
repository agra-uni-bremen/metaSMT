#include <boost/test/unit_test.hpp>
#include <string>

#include <metaSMT/support/why_unsat.hpp>
#include <metaSMT/support/contradiction_analysis.hpp>
#include <metaSMT/frontend/Logic.hpp>

#include <boost/assign/list_of.hpp>
#include <boost/fusion/adapted/boost_tuple.hpp>
#include <algorithm>
#define foreach BOOST_FOREACH

using namespace std;
using namespace metaSMT;
using namespace metaSMT::solver;
using namespace metaSMT::logic;
namespace proto = boost::proto;
using boost::dynamic_bitset;
using boost::assign::list_of;

std::ostream & operator<< (std::ostream & out, vector<unsigned> const & v)
{
 out <<"( ";
 foreach(unsigned u, v)  {
   out << u << ' ';
 }
 out <<')';
 return out;
}

std::ostream & operator<< (std::ostream & out, vector<vector<unsigned> > const & v)
{
 out <<"( ";
 foreach(vector<unsigned> const & u, v)  {
   out << u << ' ';
 }
 out <<')';
 return out;
}

//vergleich von vector<unsigned>
bool cmp_vec(std::vector<unsigned> const &a, std::vector<unsigned> const &b)
{
	if(a.size() == b.size())
	{
		for (unsigned i = 0; i < a.size(); i++) {
			if(a[i] != b[i])
			{
			  return a[i] < b[i];
			}
		}
	} else {
		return a.size() < b.size();
	}
  return false;
}

//sortieren
void sort_results( std::vector<std::vector<unsigned> > &results )
{
	for(unsigned i = 0; i < results.size();i++)
	{
	  sort(results[i].begin(), results[i].end());
	}
	  sort(results.begin(), results.end(), cmp_vec);
}


BOOST_FIXTURE_TEST_SUITE(unsat, Solver_Fixture )

BOOST_AUTO_TEST_CASE( why_unsat1 )
{
  BOOST_REQUIRE( solve(ctx) );

  predicate b = new_variable();
  predicate c = new_variable();
  predicate d = new_variable();
  
  vector<bool> result =
    why_unsat(ctx, boost::make_tuple( Xor(d,c), b, equal(b,c), d, Not(c) ) );

  print_why_unsat(ctx, boost::make_tuple( Xor(d,c), b, equal(b,c), d, Not(c) ) );
  
  vector<bool> expected = 
    boost::assign::list_of(false)(true)(true)(false)(true);
  BOOST_REQUIRE_EQUAL_COLLECTIONS( result.begin(), result.end(), expected.begin(), expected.end());
}

BOOST_AUTO_TEST_CASE( one_true )
{
  BOOST_REQUIRE( solve(ctx) );

  predicate b = new_variable();
  predicate c = new_variable();
  predicate d = new_variable();
  
  vector< vector<unsigned> > result =
     contradiction_analysis(ctx, boost::make_tuple( True ) );

  cout << result << endl;
  //std::cout << result.size() << std::endl;
  BOOST_REQUIRE_EQUAL(result.size(), 0);
}

BOOST_AUTO_TEST_CASE( one_true_vec )
{
  BOOST_REQUIRE( solve(ctx) );
  typedef ContextType::result_type result_type;
  
  result_type x = evaluate(ctx,True);

  vector<result_type> vec;
  vec.push_back(x);
  
  vector< vector<unsigned> > result =
    contradiction_analysis(ctx, vec );

  cout << result << endl;

  //std::cout << result.size() << std::endl;
  BOOST_REQUIRE_EQUAL(result.size(), 0);
}

BOOST_AUTO_TEST_CASE( one_false )
{
  BOOST_REQUIRE( solve(ctx) );

  predicate b = new_variable();
  predicate c = new_variable();
  predicate d = new_variable();
  
  vector< vector<unsigned> > result =
     contradiction_analysis(ctx, boost::make_tuple( False ));

  cout << result << endl;
  //cout << result.size() << " result.size() " << endl;

  BOOST_REQUIRE_EQUAL(result.size(), 1);

}

BOOST_AUTO_TEST_CASE( one_false_vec )
{
  BOOST_REQUIRE( solve(ctx) );
  typedef ContextType::result_type result_type;
  
  result_type x = evaluate(ctx,False);

  vector<result_type> vec;
  vec.push_back(x);
  
  vector< vector<unsigned> > result =
    contradiction_analysis(ctx, vec );

  cout << result << endl;

  BOOST_REQUIRE_EQUAL(result.size(), 1);

}

BOOST_AUTO_TEST_CASE( two_false )
{
  BOOST_REQUIRE( solve(ctx) );

  predicate b = new_variable();
  predicate c = new_variable();
  predicate d = new_variable();
  
  vector< vector<unsigned> > result =
      contradiction_analysis(ctx, boost::make_tuple( False, False ));


  cout << result << endl;
  //cout << result.size() << " result.size() " << endl;

  BOOST_REQUIRE_EQUAL(result.size(), 2);
  BOOST_REQUIRE_EQUAL(result[0].size(), 1);
  BOOST_REQUIRE_EQUAL(result[1].size(), 1);
  BOOST_REQUIRE(result[0][0]==0 || result[1][0]==0);
  BOOST_REQUIRE(result[0][0]==1 || result[1][0]==1);

}

BOOST_AUTO_TEST_CASE( two_false_vec )
{
  BOOST_REQUIRE( solve(ctx) );
  typedef ContextType::result_type result_type;
  
  result_type x = evaluate(ctx,False);
  result_type y = evaluate(ctx,False);
  
  vector<result_type> vec;
  vec.push_back(x);
  vec.push_back(y);

  vector< vector<unsigned> > result =
    contradiction_analysis(ctx, vec );

  cout << result << endl;
  //cout << result.size() << " result.size() " << endl;

  BOOST_REQUIRE_EQUAL(result.size(), 2);
  BOOST_REQUIRE_EQUAL(result[0].size(), 1);
  BOOST_REQUIRE_EQUAL(result[1].size(), 1);
  BOOST_REQUIRE(result[0][0]==0 || result[1][0]==0);
  BOOST_REQUIRE(result[0][0]==1 || result[1][0]==1);

}

BOOST_AUTO_TEST_CASE( three_false )
{
  BOOST_REQUIRE( solve(ctx) );

  predicate b = new_variable();
  predicate c = new_variable();
  predicate d = new_variable();
  
  vector< vector<unsigned> > result =
    contradiction_analysis(ctx, boost::make_tuple(False, False, False) );

  cout << result << endl;
  //cout << result.size() << " result.size() " << endl;

  BOOST_REQUIRE_EQUAL(result.size(), 3);
  BOOST_REQUIRE_EQUAL(result[0].size(), 1);
  BOOST_REQUIRE_EQUAL(result[1].size(), 1);
  BOOST_REQUIRE_EQUAL(result[2].size(), 1);
  BOOST_REQUIRE(result[0][0] == 0 || result[1][0] == 0 || result[2][0] == 0);
  BOOST_REQUIRE(result[0][0] == 1 || result[1][0] == 1 || result[2][0] == 1);
  BOOST_REQUIRE(result[0][0] == 2 || result[1][0] == 2 || result[2][0] == 2);
   

}

BOOST_AUTO_TEST_CASE( three_false_vec )
{
  BOOST_REQUIRE( solve(ctx) );
  typedef ContextType::result_type result_type;
  
  result_type x = evaluate(ctx,False);
  result_type y = evaluate(ctx,False);
  result_type z = evaluate(ctx,False);
  vector<result_type> vec;
  vec.push_back(x);
  vec.push_back(y);
  vec.push_back(z);

  vector< vector<unsigned> > result =
    contradiction_analysis(ctx, vec );

  cout << result << endl;
  //cout << result.size() << " result.size() " << endl;

  BOOST_REQUIRE_EQUAL(result.size(), 3);
  BOOST_REQUIRE_EQUAL(result[0].size(), 1);
  BOOST_REQUIRE_EQUAL(result[1].size(), 1);
  BOOST_REQUIRE_EQUAL(result[2].size(), 1);
  BOOST_REQUIRE(result[0][0] == 0 || result[1][0] == 0 || result[2][0] == 0);
  BOOST_REQUIRE(result[0][0] == 1 || result[1][0] == 1 || result[2][0] == 1);
  BOOST_REQUIRE(result[0][0] == 2 || result[1][0] == 2 || result[2][0] == 2);
}

BOOST_AUTO_TEST_CASE( two_conflicts_1 )
{
  BOOST_REQUIRE( solve(ctx) );

  predicate b = new_variable();
  predicate c = new_variable();
  predicate d = new_variable();
  
  vector< vector<unsigned> > result =
    contradiction_analysis(ctx, boost::make_tuple(True, False, nequal(d,b), equal(d, b) ));
  sort_results(result);

  cout << result << endl;
  //cout << result.size() << " result.size() " << endl;

  BOOST_REQUIRE_EQUAL(result.size(), 2);
  BOOST_REQUIRE_EQUAL(result[0].size(), 1);
  BOOST_REQUIRE_EQUAL(result[1].size(), 2);
  BOOST_REQUIRE_EQUAL(result[0][0], 1);

  vector<unsigned> expected = list_of (2)(3);
  BOOST_REQUIRE_EQUAL_COLLECTIONS( result[1].begin(), result[1].end(), expected.begin(), expected.end());
}

BOOST_AUTO_TEST_CASE( two_conflicts_1_vec )
{
  BOOST_REQUIRE( solve(ctx) );
  typedef ContextType::result_type result_type;
  
  predicate b = new_variable();
  predicate c = new_variable();

  result_type x = evaluate(ctx,True);
  result_type y = evaluate(ctx,False);
  result_type z1 = evaluate(ctx,nequal(b,c));
  result_type z2 = evaluate(ctx,equal(b,c));

  vector<result_type> vec;
  vec.push_back(x);
  vec.push_back(y);
  vec.push_back(z1);
  vec.push_back(z2);

  vector< vector<unsigned> > result =
    contradiction_analysis(ctx, vec );
  
  sort_results(result);

  cout << result << endl;
  //cout << result.size() << " result.size() " << endl;

  BOOST_REQUIRE_EQUAL(result.size(), 2);
  BOOST_REQUIRE_EQUAL(result[0].size(), 1);
  BOOST_REQUIRE_EQUAL(result[1].size(), 2);
  BOOST_REQUIRE_EQUAL(result[0][0], 1);

  vector<unsigned> expected = list_of (2)(3);
  BOOST_REQUIRE_EQUAL_COLLECTIONS( result[1].begin(), result[1].end(), expected.begin(), expected.end());
}

BOOST_AUTO_TEST_CASE( two_conflicts_2 )
{
  BOOST_REQUIRE( solve(ctx) );

  predicate b = new_variable();
  predicate c = new_variable();
  predicate d = new_variable();
  
  vector< vector<unsigned> > result =
    contradiction_analysis(ctx, boost::make_tuple(equal(c,b), nequal(d,b), nequal(c,b), equal(d, b) ));
  sort_results(result);

  cout << result << endl;
  //cout << result.size() << " result.size() " << endl;

  BOOST_REQUIRE_EQUAL(result.size(), 2);
  BOOST_REQUIRE_EQUAL(result[0].size(), 2);
  BOOST_REQUIRE_EQUAL(result[1].size(), 2);
  vector<unsigned> expected;

  expected= list_of (0)(2);
  BOOST_REQUIRE_EQUAL_COLLECTIONS( result[0].begin(), result[0].end(), expected.begin(), expected.end());

  expected= list_of (1)(3);
  BOOST_REQUIRE_EQUAL_COLLECTIONS( result[1].begin(), result[1].end(), expected.begin(), expected.end());
}

BOOST_AUTO_TEST_CASE( two_conflicts_2_vec )
{
  BOOST_REQUIRE( solve(ctx) );
  typedef ContextType::result_type result_type;
  
  predicate a = new_variable();
  predicate b = new_variable();
  predicate c = new_variable();
 
  result_type x1 = evaluate(ctx,equal(a,b));
  result_type x2 = evaluate(ctx,nequal(c,b));
  result_type z1 = evaluate(ctx,nequal(a,b));
  result_type z2 = evaluate(ctx,equal(b,c));

  vector<result_type> vec;
  vec.push_back(x1);
  vec.push_back(x2);
  vec.push_back(z1);
  vec.push_back(z2);

  vector< vector<unsigned> > result =
    contradiction_analysis(ctx, vec );
  
  sort_results(result);

  cout << result << endl;
  //cout << result.size() << " result.size() " << endl;

  BOOST_REQUIRE_EQUAL(result.size(), 2);
  BOOST_REQUIRE_EQUAL(result[0].size(), 2);
  BOOST_REQUIRE_EQUAL(result[1].size(), 2);
  vector<unsigned> expected;

  expected= list_of (0)(2);
  BOOST_REQUIRE_EQUAL_COLLECTIONS( result[0].begin(), result[0].end(), expected.begin(), expected.end());

  expected= list_of (1)(3);
  BOOST_REQUIRE_EQUAL_COLLECTIONS( result[1].begin(), result[1].end(), expected.begin(), expected.end());
}

BOOST_AUTO_TEST_CASE( two_conflicts_3 )
{
  BOOST_REQUIRE( solve(ctx) );

  predicate b = new_variable();
  predicate c = new_variable();
  predicate d = new_variable();
  
  vector< vector<unsigned> > result =
    contradiction_analysis(ctx, boost::make_tuple(True, nequal(d,b), False, equal(d, b) ));
  sort_results(result);

  cout << result << endl;
 // cout << result.size() << " result.size() " << endl;

  BOOST_REQUIRE_EQUAL(result.size(), 2);
  BOOST_REQUIRE_EQUAL(result[0].size(), 1);
  BOOST_REQUIRE_EQUAL(result[1].size(), 2);
  BOOST_REQUIRE_EQUAL(result[0][0], 2);

  vector<unsigned> expected = list_of (1)(3);
  BOOST_REQUIRE_EQUAL_COLLECTIONS( result[1].begin(), result[1].end(), expected.begin(), expected.end());
}

BOOST_AUTO_TEST_CASE( two_conflicts_3_vec )
{
  BOOST_REQUIRE( solve(ctx) );
  typedef ContextType::result_type result_type;
  
  predicate a = new_variable();
  predicate b = new_variable();
  predicate c = new_variable();
 
  result_type x1 = evaluate(ctx,True);
  result_type x2 = evaluate(ctx,nequal(a,b));
  result_type z1 = evaluate(ctx,False);
  result_type z2 = evaluate(ctx,equal(a,b));

  vector<result_type> vec;
  vec.push_back(x1);
  vec.push_back(x2);
  vec.push_back(z1);
  vec.push_back(z2);

  vector< vector<unsigned> > result =
    contradiction_analysis(ctx, vec );
  
  sort_results(result);

  cout << result << endl;
 // cout << result.size() << " result.size() " << endl;

  BOOST_REQUIRE_EQUAL(result.size(), 2);
  BOOST_REQUIRE_EQUAL(result[0].size(), 1);
  BOOST_REQUIRE_EQUAL(result[1].size(), 2);
  BOOST_REQUIRE_EQUAL(result[0][0], 2);

  vector<unsigned> expected = list_of (1)(3);
  BOOST_REQUIRE_EQUAL_COLLECTIONS( result[1].begin(), result[1].end(), expected.begin(), expected.end());
}

BOOST_AUTO_TEST_CASE( double_conflict_1 )
{
  BOOST_REQUIRE( solve(ctx) );
  
  predicate b = new_variable();
  predicate c = new_variable();
  predicate d = new_variable();
  
  vector< vector<unsigned> > result =
    contradiction_analysis(ctx, boost::make_tuple(True, nequal(d,b), equal(d, b), nequal(d,b) ));
  sort_results(result);

  cout << result << endl;
 // cout << result.size() << " result.size() " << endl;

  BOOST_REQUIRE_EQUAL(result.size(), 2);
  BOOST_REQUIRE_EQUAL(result[0].size(), 2);
  BOOST_REQUIRE_EQUAL(result[1].size(), 2);

vector<unsigned> expected;

  expected = list_of (1)(2);
  BOOST_REQUIRE_EQUAL_COLLECTIONS( result[0].begin(), result[0].end(), expected.begin(), expected.end());

  expected = list_of (2)(3);
  BOOST_REQUIRE_EQUAL_COLLECTIONS( result[1].begin(), result[1].end(), expected.begin(), expected.end());
}

BOOST_AUTO_TEST_CASE( double_conflict_1_vec )
{
  BOOST_REQUIRE( solve(ctx) );
  typedef ContextType::result_type result_type;
  
  predicate a = new_variable();
  predicate b = new_variable();
  predicate c = new_variable();
 
  result_type x1 = evaluate(ctx,True);
  result_type x2 = evaluate(ctx,nequal(a,b));
  result_type z1 = evaluate(ctx,equal(a,b));
  result_type z2 = evaluate(ctx,nequal(a,b));

  vector<result_type> vec;
  vec.push_back(x1);
  vec.push_back(x2);
  vec.push_back(z1);
  vec.push_back(z2);

  vector< vector<unsigned> > result =
    contradiction_analysis(ctx, vec );
  
  sort_results(result);

  cout << result << endl;
 // cout << result.size() << " result.size() " << endl;

  BOOST_REQUIRE_EQUAL(result.size(), 2);
  BOOST_REQUIRE_EQUAL(result[0].size(), 2);
  BOOST_REQUIRE_EQUAL(result[1].size(), 2);

vector<unsigned> expected;

  expected = list_of (1)(2);
  BOOST_REQUIRE_EQUAL_COLLECTIONS( result[0].begin(), result[0].end(), expected.begin(), expected.end());

  expected = list_of (2)(3);
  BOOST_REQUIRE_EQUAL_COLLECTIONS( result[1].begin(), result[1].end(), expected.begin(), expected.end());
}

BOOST_AUTO_TEST_CASE( double_conflicts_1)
{
  BOOST_REQUIRE( solve(ctx) );

  predicate b = new_variable();
  predicate c = new_variable();
  predicate d = new_variable(); 
  predicate a = new_variable();
  
  vector< vector<unsigned> > result =
    contradiction_analysis(ctx, boost::make_tuple( True, equal(d,b), False, nequal(d,b), False, equal(a,c), nequal(a,c), True ) );
 
//  sort_results(result);

  cout << result << endl;
  //cout << result.size() << " result.size() " << endl;

  BOOST_REQUIRE_EQUAL(result.size(), 4);
  BOOST_REQUIRE_EQUAL(result[0].size(), 2);
  BOOST_REQUIRE_EQUAL(result[1].size(), 1);
  BOOST_REQUIRE_EQUAL(result[2].size(), 1);
  BOOST_REQUIRE_EQUAL(result[3].size(), 2);

   vector<unsigned> expected;

  expected = list_of (1)(3);
  BOOST_REQUIRE_EQUAL_COLLECTIONS( result[0].begin(), result[0].end(), expected.begin(), expected.end());
 
    expected = list_of (5)(6);
  BOOST_REQUIRE_EQUAL_COLLECTIONS( result[3].begin(), result[3].end(), expected.begin(), expected.end());
}

BOOST_AUTO_TEST_CASE( double_conflicts_1_vec)
{
  BOOST_REQUIRE( solve(ctx) );
  typedef ContextType::result_type result_type;
  
  predicate a = new_variable();
  predicate b = new_variable();
  predicate c = new_variable();
  predicate d = new_variable();

  result_type x1 = evaluate(ctx,True);
  result_type x2 = evaluate(ctx,equal(a,b));
  result_type x3 = evaluate(ctx,False);
  result_type x4 = evaluate(ctx,nequal(a,b));
  result_type x5 = evaluate(ctx,False);
  result_type x6 = evaluate(ctx,equal(c,d));
  result_type x7 = evaluate(ctx,nequal(c,d));
  result_type x8 = evaluate(ctx,True);

  vector<result_type> vec;
  vec.push_back(x1);
  vec.push_back(x2);
  vec.push_back(x3);
  vec.push_back(x4);
  vec.push_back(x5);
  vec.push_back(x6);
  vec.push_back(x7);
  vec.push_back(x8);

  vector< vector<unsigned> > result =
    contradiction_analysis(ctx, vec );
  
  //sort_results(result);

  cout << result << endl;
  //cout << result.size() << " result.size() " << endl;

  BOOST_REQUIRE_EQUAL(result.size(), 4);
  BOOST_REQUIRE_EQUAL(result[0].size(), 2);
  BOOST_REQUIRE_EQUAL(result[1].size(), 1);
  BOOST_REQUIRE_EQUAL(result[2].size(), 1);
  BOOST_REQUIRE_EQUAL(result[3].size(), 2);

   vector<unsigned> expected;

  expected = list_of (1)(3);
  BOOST_REQUIRE_EQUAL_COLLECTIONS( result[0].begin(), result[0].end(), expected.begin(), expected.end());
 
    expected = list_of (5)(6);
  BOOST_REQUIRE_EQUAL_COLLECTIONS( result[3].begin(), result[3].end(), expected.begin(), expected.end());
}

BOOST_AUTO_TEST_CASE( unsolve_conflict)
{
  BOOST_REQUIRE( solve(ctx) );

  predicate a = new_variable();
  predicate b = new_variable();
  predicate c = new_variable();
  
  vector< vector<unsigned> > result =
    contradiction_analysis(ctx, boost::make_tuple( nequal(a,b), nequal(b,c), nequal(a,c)) );


  cout << result << endl;
  //cout << result.size() << " result.size() " << endl;

  BOOST_REQUIRE_EQUAL(result.size(), 1);
  vector<unsigned> expected;

  expected = list_of (0)(1)(2);
  BOOST_REQUIRE_EQUAL_COLLECTIONS( result[0].begin(), result[0].end(), expected.begin(), expected.end());
}

BOOST_AUTO_TEST_CASE( unsolve_conflict_vec)
{
  BOOST_REQUIRE( solve(ctx) );
  typedef ContextType::result_type result_type;
  
  predicate a = new_variable();
  predicate b = new_variable();
  predicate c = new_variable();

  result_type x1 = evaluate(ctx,nequal(a,b));
  result_type x2 = evaluate(ctx,nequal(b,c));
  result_type x3 = evaluate(ctx,nequal(a,c));

  vector<result_type> vec;
  vec.push_back(x1);
  vec.push_back(x2);
  vec.push_back(x3);

  vector< vector<unsigned> > result =
    contradiction_analysis(ctx, vec );
  
  //sort_results(result);

  cout << result << endl;
  //cout << result.size() << " result.size() " << endl;

  BOOST_REQUIRE_EQUAL(result.size(), 1);
  vector<unsigned> expected;

  expected = list_of (0)(1)(2);
  BOOST_REQUIRE_EQUAL_COLLECTIONS( result[0].begin(), result[0].end(), expected.begin(), expected.end());
}

/*
BOOST_AUTO_TEST_CASE( con_checking1 )
{
  BOOST_REQUIRE( solve(ctx) );

  predicate b = new_variable();
  predicate c = new_variable();
  predicate d = new_variable();
  
  vector< vector<unsigned> > result =
    con_checking(ctx, boost::make_tuple(False, True) );

  cout << result << endl;
  cout << result.size() << " result.size() " << endl;

  BOOST_REQUIRE_EQUAL(result.size(), 1);
  
  BOOST_REQUIRE_EQUAL(result[0].size(), 1);
  BOOST_REQUIRE_EQUAL(result[1].size(), 1);
  BOOST_REQUIRE_EQUAL(result[2].size(), 1);
  BOOST_REQUIRE(result[0][0] == 0 || result[1][0] == 0 || result[2][0] == 0);
  BOOST_REQUIRE(result[0][0] == 1 || result[1][0] == 1 || result[2][0] == 1);
  BOOST_REQUIRE(result[0][0] == 2 || result[1][0] == 2 || result[2][0] == 2);
  
}
*/
BOOST_AUTO_TEST_SUITE_END() //Solver

//  vim: ft=cpp:ts=2:sw=2:expandtab
