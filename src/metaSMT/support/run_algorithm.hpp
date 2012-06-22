#pragma once

#include <boost/mpl/for_each.hpp>
#include <boost/mpl/at.hpp>
#include <boost/mpl/empty.hpp>
#include <boost/static_assert.hpp>
#include <boost/type_traits/add_pointer.hpp>
#include <boost/shared_ptr.hpp>

namespace metaSMT
{
  namespace mpl = boost::mpl; 

  template<typename Vec, template<class T> class Algo> 
  class eval_visitor 
  {
    public:
      typedef typename Algo<typename mpl::at_c <Vec, 0>::type>::result_type result_type;

      eval_visitor (unsigned wanted) : 
         wanted_ (wanted) 
       , result_ ( new result_type ) 
      {
        //       BOOST_STATIC_ASSERT ( !typename mpl::empty < Vec >::value ); 
      } 
      result_type get_result() const
      {
        return *result_;
      }

    protected:
      unsigned wanted_; 
      boost::shared_ptr < result_type > result_; 
  };

  template<typename Vec, template<class T> class Algo>
  struct eval_visitor_0 : public eval_visitor < Vec, Algo > 
  {
    eval_visitor_0 ( unsigned wanted ) 
      : eval_visitor<Vec, Algo> ( wanted ) 
    {}

    template<typename U>
      void operator() (U const &)
      {
        typedef typename mpl::find < Vec,U>::type iter; 
        unsigned pos = iter::pos::value;              

        if (pos == eval_visitor<Vec,Algo>::wanted_)
        {
          Algo< U > algo;
          *eval_visitor<Vec,Algo>::result_ = algo (); 
        }
      }
  }; 


  template<typename Vec, template<class T> class Algo, typename ARG0>
  struct eval_visitor_1 : public eval_visitor < Vec, Algo > 
  {
    eval_visitor_1 (unsigned wanted, ARG0 arg0) :
        eval_visitor < Vec, Algo > ( wanted )
      , arg0_ (arg0) {}

    template<typename U>
      void operator() (U*)
      {
        typedef typename mpl::find < Vec,U>::type iter; 
        unsigned pos = iter::pos::value;              

        if (pos == eval_visitor<Vec,Algo>::wanted_)
        {
          Algo< U > algo ( arg0_ );
          *eval_visitor<Vec,Algo>::result_ = algo (); 
        }
      }

    private:
      ARG0 arg0_; 
  }; 

  template<typename Vec, template<class T> class Algo, typename ARG0, typename ARG1>
  struct eval_visitor_2 : public eval_visitor < Vec, Algo > 
  {
    eval_visitor_2 (unsigned wanted, ARG0 arg0, ARG1 arg1) :
        eval_visitor < Vec, Algo > ( wanted )
      , arg0_ (arg0)
      , arg1_ (arg1) {}

    template<typename U>
      void operator() (U *)
      {
        typedef typename mpl::find < Vec,U>::type iter; 
        unsigned pos = iter::pos::value;              

        if (pos == eval_visitor<Vec,Algo>::wanted_)
        {
          Algo< U > algo ( arg0_ , arg1_ );
          *eval_visitor<Vec,Algo>::result_ = algo (); 
        }
      }

    private:
      ARG0 arg0_; 
      ARG1 arg1_; 
  }; 

  template<typename Vec, template<class T> class Algo, typename ARG0, typename ARG1, typename ARG2>
  struct eval_visitor_3 : public eval_visitor < Vec, Algo > 
  {
    eval_visitor_3 (unsigned wanted, ARG0 arg0, ARG1 arg1, ARG2 arg2) :
        eval_visitor < Vec, Algo > ( wanted )
      , arg0_ (arg0)
      , arg1_ (arg1)
      , arg2_ (arg2) {}

    template<typename U>
      void operator() (U*)
      {
        typedef typename mpl::find < Vec,U>::type iter; 
        unsigned pos = iter::pos::value;              

        if (pos == eval_visitor<Vec,Algo>::wanted_)
        {
          Algo< U > algo ( arg0_ , arg1_ , arg2_ );
          *eval_visitor<Vec,Algo>::result_ = algo (); 
        }
      }

    private:
      ARG0 arg0_; 
      ARG1 arg1_; 
      ARG2 arg2_; 
  }; 

  template<typename Vec, template<class T> class Algo, typename ARG0, typename ARG1, typename ARG2, typename ARG3>
  struct eval_visitor_4 : public eval_visitor < Vec, Algo > 
  {
    eval_visitor_4 (unsigned wanted, ARG0 arg0, ARG1 arg1, ARG2 arg2, ARG3 arg3) :
        eval_visitor < Vec, Algo > ( wanted )
      , arg0_ (arg0)
      , arg1_ (arg1)
      , arg2_ (arg2)
      , arg3_ (arg3) {}

    template<typename U>
      void operator() (U*)
      {
        typedef typename mpl::find < Vec,U>::type iter; 
        unsigned pos = iter::pos::value;              

        if (pos == eval_visitor<Vec,Algo>::wanted_)
        {
          Algo< U > algo ( arg0_ , arg1_ , arg2_, arg3_ );
          *eval_visitor<Vec,Algo>::result_ = algo (); 
        }
      }

    private:
      ARG0 arg0_; 
      ARG1 arg1_; 
      ARG2 arg2_; 
      ARG3 arg3_; 
  }; 

  template<typename Vec, template<class T> class Algo, typename ARG0, typename ARG1, typename ARG2, typename ARG3, typename ARG4>
  struct eval_visitor_5 : public eval_visitor < Vec, Algo > 

  {
    eval_visitor_5 (unsigned wanted, ARG0 arg0, ARG1 arg1, ARG2 arg2, ARG3 arg3, ARG4 arg4) :
        eval_visitor < Vec, Algo > ( wanted )
      , arg0_ (arg0)
      , arg1_ (arg1)
      , arg2_ (arg2)
      , arg3_ (arg3)
      , arg4_ (arg4) {}

    template<typename U>
      void operator() (U*)
      {
        typedef typename mpl::find < Vec,U>::type iter; 
        unsigned pos = iter::pos::value;              

        if (pos == eval_visitor<Vec,Algo>::wanted_)
        {
          Algo< U > algo ( arg0_ , arg1_ , arg2_, arg3_, arg4_ );
          *eval_visitor<Vec,Algo>::result_ = algo (); 
        }
      }

    private:
      ARG0 arg0_; 
      ARG1 arg1_; 
      ARG2 arg2_; 
      ARG3 arg3_; 
      ARG4 arg4_;
  }; 


  template<typename Vec, template<class T> class Algo>
  typename eval_visitor<Vec, Algo>::result_type run_algorithm ( unsigned wanted )
  {
    eval_visitor_0<Vec, Algo> visitor ( wanted );
    mpl::for_each<Vec, boost::add_pointer<mpl::_> > (visitor);

    return visitor.get_result (); 
  }

 template<typename Vec, template<class T> class Algo, typename ARG0>
  typename eval_visitor<Vec, Algo>::result_type run_algorithm ( unsigned wanted, ARG0 arg0 )
  {
    eval_visitor_1<Vec, Algo, ARG0> visitor ( wanted, arg0 );
    mpl::for_each<Vec, boost::add_pointer<mpl::_> > (visitor);

    return visitor.get_result (); 
  }

 template<typename Vec, template<class T> class Algo, typename ARG0, typename ARG1>
  typename eval_visitor<Vec, Algo>::result_type run_algorithm ( unsigned wanted, ARG0 arg0, ARG1 arg1 )
  {
    eval_visitor_2<Vec, Algo, ARG0, ARG1> visitor ( wanted, arg0, arg1 );
    mpl::for_each<Vec, boost::add_pointer<mpl::_> > (visitor);

    return visitor.get_result (); 
  }

 template<typename Vec, template<class T> class Algo, typename ARG0, typename ARG1, typename ARG2>
  typename eval_visitor<Vec, Algo>::result_type run_algorithm ( unsigned wanted, ARG0 arg0, ARG1 arg1, ARG2 arg2 )
  {
    eval_visitor_3<Vec, Algo, ARG0, ARG1, ARG2> visitor ( wanted, arg0, arg1, arg2 );
    mpl::for_each<Vec, boost::add_pointer<mpl::_> > (visitor);

    return visitor.get_result (); 
  }

 template<typename Vec, template<class T> class Algo, typename ARG0, typename ARG1, typename ARG2, typename ARG3 >
  typename eval_visitor<Vec, Algo>::result_type run_algorithm ( unsigned wanted, ARG0 arg0, ARG1 arg1, ARG2 arg2, ARG3 arg3 )
  {
    eval_visitor_4<Vec, Algo, ARG0, ARG1, ARG2, ARG3> visitor ( wanted, arg0, arg1, arg2, arg3 );
    mpl::for_each<Vec, boost::add_pointer<mpl::_> > (visitor);

    return visitor.get_result (); 
  }

 template<typename Vec, template<class T> class Algo, typename ARG0, typename ARG1, typename ARG2, typename ARG3, typename ARG4 >
  typename eval_visitor<Vec, Algo>::result_type run_algorithm ( unsigned wanted, ARG0 arg0, ARG1 arg1, ARG2 arg2, ARG3 arg3, ARG4 arg4 )
  {
    eval_visitor_5<Vec, Algo, ARG0, ARG1, ARG2, ARG3, ARG4> visitor ( wanted, arg0, arg1, arg2, arg3, arg4 );
    mpl::for_each<Vec, boost::add_pointer<mpl::_> > (visitor);

    return visitor.get_result (); 
  }


 


}


