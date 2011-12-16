#pragma once
#include <boost/random/mersenne_twister.hpp>
#include <boost/utility/enable_if.hpp>
#include <boost/random/uniform_int.hpp>
#include <boost/function.hpp>
#include "../Features.hpp"
#include "../frontend/QF_BV.hpp"
#include "../frontend/Logic.hpp"
#include "Assumption.hpp"

namespace preds = metaSMT::logic;
namespace qf_bv = metaSMT::logic::QF_BV;

using metaSMT::assumption;
using metaSMT::evaluate;

namespace metaSMT {

  struct assign_random_bits_cmd {typedef void result_type;};
  struct solve_random_bits_cmd  {typedef bool result_type;};

  template <typename Context >
  struct IgnoreAssignRandomBits : Context {
  	void command (assign_random_bits_cmd const &, std::vector<metaSMT::logic::QF_BV::bitvector>& _variables){
  	 /* ignored */  	
        }
        using Context::command;
  };
 
 template <typename Context>
 struct AssignRandomBits : Context {
 	template<typename Self>
 	void command(assign_random_bits_cmd const &, Self & ctx, std::vector<metaSMT::logic::QF_BV::bitvector> const& _variables)
   	{
 	  std::vector <typename Context::result_type> bits;

          typedef metaSMT::logic::QF_BV::bitvector bitvec;
          BOOST_FOREACH( bitvec const & p, _variables ) {
          for(unsigned i=0; i < proto::value(p).width; ++i) {
          typename Context::result_type tmp = evaluate(ctx, extract( i,i, p));
            //extract(i,i, p));
          bits.push_back(tmp);
         }
       
      }
      std::random_shuffle(bits.begin(),bits.end());
      int len = bits.size() > 0 ? boost::uniform_int<int>(0, bits.size() - 1)(rng) : 0;     
      for(int i = 0; i < len ; ++i) {
       metaSMT::assumption(ctx, metaSMT::logic::equal(bits[i], metaSMT::logic::QF_BV::bvuint(boost::uniform_int<int>(0, 1)(rng), 1)));
      }
   }	
 	  

template<typename Self>
	bool command(solve_random_bits_cmd const&, Self& ctx, std::vector<metaSMT::logic::QF_BV::bitvector>const& variables, unsigned max_retries ) {
		command(assign_random_bits_cmd(), ctx, variables); // setzt einige random_bits
		if(Context::solve()) // wenn erfüllbar, dann true; solve(ctx)?
			return true;
		if(!Context::solve()) // wenn unerfüllbar, dann false
			return false;
		for (unsigned i = 0; i < max_retries; i++) {
			command(assign_random_bits_cmd(), ctx, variables); // setzt einige random_bits
			if(Context::solve()) // solve(ctx)?
				return true;
		}
		return Context::solve();
	}//end command

 	using Context::command;
 
  protected:
  boost::mt19937 rng;  
   };
   
  namespace features {
  /* AssignRandomBits supports stack api */
   template<typename Context>
   struct supports<  IgnoreAssignRandomBits<Context>, assign_random_bits_cmd>
    : boost::mpl::true_ {};

    /* Forward all other supported operations */
    template<typename Context, typename Feature>
    struct supports<  IgnoreAssignRandomBits<Context>, Feature>
    : supports<Context, Feature>::type {};

   template<typename Context>
   struct supports<AssignRandomBits<Context>, assign_random_bits_cmd>
    : boost::mpl::true_ {};

   template<typename Context>
   struct supports<AssignRandomBits<Context>, solve_random_bits_cmd>
    : boost::mpl::true_ {};


    /* Forward all other supported operations */
   template<typename Context, typename Feature>
   struct supports< AssignRandomBits<Context>, Feature>
    : supports<Context, Feature>::type {};
  }
  
  template< typename Context >
  void assign_random_bits(Context & ctx, std::vector<metaSMT::logic::QF_BV::bitvector>& _variables)  {
   BOOST_MPL_ASSERT_MSG(( features::supports<Context, assign_random_bits_cmd>::value ),
        context_does_not_support_assign_random_bits_api, (Context) );
    ctx.command(assign_random_bits_cmd(), ctx, _variables);
  }

template< typename Context >
  bool solve_with_random_bits(Context & ctx, std::vector<metaSMT::logic::QF_BV::bitvector>& _variables, unsigned max_retries = 10)  {
   BOOST_MPL_ASSERT_MSG(( features::supports<Context, solve_random_bits_cmd>::value ),
        context_does_not_support_solve_random_bits_api, (Context) );
    return ctx.command(solve_random_bits_cmd(), ctx, _variables, max_retries);
  }



}//namespace metaSMT    
