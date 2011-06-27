#pragma once

#include "../impl/_var_id.hpp" 
#include "../tags/Logic.hpp" 
#include "../Features.hpp" 

#include <cstdio>
#include <vector>

#include <boost/proto/debug.hpp>
#include <boost/any.hpp>
#include <boost/foreach.hpp>
#include <boost/tr1/unordered_map.hpp>
#include <boost/mpl/assert.hpp>

 
namespace metaSMT {
  /**
   * \ingroup Group
   */
  typedef unsigned guard_type; 


  namespace features {
    struct group_api {};
  } /* features */

  struct group_change { typedef void result_type; };
  struct group_create { typedef guard_type result_type; };
  struct group_delete { typedef void result_type; };
  struct group_current { typedef guard_type result_type; };

  /**
   * \brief assertion groups.
   *
   * An API that allows grouping of constraints. groups can be freely created
   * and destroyed. The assertions and assumptions are automatically added to 
   * the currently selected group. Changing group is possible at any time.
   *
   * Groups are created by adding a guard variable (implication) to each
   * expression.
   *
   * \code
   *  // enable Group API for ctx
   *  DirectSolver_Context< Group<Context> > ctx;
   *  guard_type main = current_group(ctx);
   *
   *  // create and select a group
   *  guard_type g1 = create_group(ctx);
   *  // add assertions and solve
   *  assertion( equal(True, False);
   *  solve(ctx);
   *
   *  // UNSAT, remove the Group
   *  change_group(ctx, main);
   *  delete_group(ctx, g1);
   *
   * \endcode
   *
   * Note that the current group can not be deleted because
   * the current group would be undefined or non-deterministic.
   * 
   * \ingroup API
   * \defgroup Group Assertion Groups API
   * @{
   */

  template<typename Solver>
  struct Group : public Solver 
  {
    typedef typename Solver::result_type result_type; 
    typedef std::tr1::unordered_map < guard_type, result_type > guard_map_t;
    typedef typename guard_map_t::value_type value_pair; 

    Group ()  
    {
      guard_counter_ = 0; 
      command ( group_create() ); 
    }


    void assertion ( result_type const& e )
    {
      assert ( guard_map_.find ( current_guard_ ) != guard_map_.end() ); 
      result_type guard = guard_map_ [ current_guard_ ] ;   

      Solver::assertion ( ( *this ) ( imply_, guard, e ) ); 
    }

    void assumption ( result_type const& e )
    {
      assert ( guard_map_.find ( current_guard_ ) != guard_map_.end() ); 
      result_type guard = guard_map_ [ current_guard_ ] ;   

      Solver::assumption ( ( *this ) ( imply_, guard, e ) ); 
    }

    bool solve ( ) 
    {
      BOOST_FOREACH ( value_pair g, guard_map_)
      {
        Solver::assumption ( g.second ); 
      }

      return Solver::solve () ; 
    }

    guard_type command ( group_create const &  )
    { 
      logic::tag::var_tag v = { impl::new_var_id () }; 

      current_guard_ = guard_counter_; 
      guard_map_.insert (std::make_pair (current_guard_, ( *this) ( v, boost::any() ) ) ) ; 
      ++guard_counter_; 

      return current_guard_; 
    }

    void command ( group_delete const &, guard_type guard ) 
    {
      typename guard_map_t::const_iterator iter = guard_map_.find ( guard ); 

      assert (guard != current_guard_ && "cannot delete current group" ); 
      assert (iter != guard_map_.end() && "invalid group for deletion" ); 

      Solver::assertion ( ( *this ) ( logic::tag::not_tag(), iter->second ) ); 
      guard_map_.erase ( iter ); 
    }

    guard_type command ( group_current const &  ) const 
    {
      return current_guard_; 
    }

    void command ( group_change const & , guard_type guard )
    {
      assert (guard_map_.find ( guard ) != guard_map_.end());

      current_guard_ = guard; 
    }

    using Solver::command;

    private:
      guard_type                  guard_counter_; 
      guard_map_t                 guard_map_; 
      guard_type                  current_guard_; 


      static const logic::tag::implies_tag imply_; 
  };

  namespace features {
    /* Group supports group api */
    template<typename Context>
    struct supports< Group<Context>, group_api>
    : boost::mpl::true_ {};

    /* Forward all other supported operations */
    template<typename Context, typename Feature>
    struct supports< Group<Context>, Feature>
    : supports<Context, Feature>::type {};

  } /* features */


  /* group commands */

  /**
   * \brief create a new constraint group
   * \param ctx The context to work on
   * \return a handle that identifies the group
   */
  template < typename Context > 
  guard_type create_group ( Context& ctx )
  {
    BOOST_MPL_ASSERT_MSG(
        ( features::supports< Context, features::group_api>::value),
        context_does_not_support_group_api,
    );
    return ctx.command ( group_create() ); 
  }

  /**
   * \brief delete a constraint group
   * \param ctx The context to work on
   * \param guard The group to delete
   * \return void
   *
   * Behaviour is undefined if the current group is deleted. 
   * Call change_group before deleting the current group.
   */
  template < typename Context >
  void delete_group ( Context& ctx, guard_type guard )
  {
    BOOST_MPL_ASSERT_MSG(
        ( features::supports< Context, features::group_api>::value),
        context_does_not_support_group_api,
    );
    ctx.command( group_delete(), guard ); 
  }

  /**
   * \brief change the current constraint group
   * \param ctx The context to work on
   * \param guard The group to change to
   * \return void
   *
   */
  template < typename Context >
  void change_group ( Context& ctx, guard_type guard)
  {
    BOOST_MPL_ASSERT_MSG(
        ( features::supports< Context, features::group_api>::value),
        context_does_not_support_group_api,
    );
    ctx.command ( group_change(), guard ); 
  }

  /**
   * \brief get the current group guard
   * \param ctx The context to work on
   * \return The handle for the current constraint group
   */
  template < typename Context > 
  guard_type current_group ( Context & ctx )
  {
    BOOST_MPL_ASSERT_MSG(
        ( features::supports< Context, features::group_api>::value),
        context_does_not_support_group_api,
    );
    return ctx.command( group_current() ); 
  }

  /**@}*/
} /* metaSMT */

