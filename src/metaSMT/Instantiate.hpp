#include "backend/Boolector.hpp"
#include "DirectSolver_Context.hpp"
#include "boost/mpl/list.hpp"
#include "boost/mpl/eval_if.hpp"

namespace metaSMT {

  struct boolector { 
    template <typename> struct result;
    
    template <typename This, typename Arg>
    struct result< This( Arg ) > {
      typedef solver::Boolector type;
    };

    template<typename Arg> 
    DirectSolver_Context< Arg >
    operator() (Arg) {
      return solver::Boolector();
    }
  };

  struct group { 
    template <typename> struct result;
    
    template <typename This, typename Arg>
    struct result< This( Arg ) > {
      typedef Group_Context< Arg > type;
    };

    template<typename Arg> 
    Group_Context< Arg >
    operator() (Arg) {
      return Group_Context<Arg>();
    }
  };


  struct direct { 
    template <typename> struct result;
    
    template <typename This, typename Arg>
    struct result< This( Arg ) > {
      typedef DirectSolver_Context< Arg > type;
    };

    template<typename Arg> 
    DirectSolver_Context< Arg >
    operator() (Arg) {
      return DirectSolver_Context<Arg>();
    }
  };

  template<typename A, typename B>
  struct construct_helper 
  : boost::result_of< A (B) >
  { };

  template<typename Parms>
  struct Instantiate 
  : boost::mpl::reverse_fold<Parms, boost::mpl::void_
    , construct_helper<boost::mpl::_2, boost::mpl::_1>
  >
  { 
  };

} /* metaSMT */
