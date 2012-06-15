#pragma once
#include <boost/mpl/bool.hpp>

namespace metaSMT {
  /**
   * \brief Evaluator API
   *
   * \ingroup API
   * \defgroup Evaluator Evaluator
   * @{
   */

  /**
   * \brief generic mechanism to extend the metaSMT primitives
   *
   * Evaluator provides a mechanism to enrich metaSMT's list of
   * primitives with arbitary types.  For each new type T a
   * specialization of metaSMT::Evaluator<T> has to be implemened
   * which provides a static member function eval(.) to convert the
   * new type into a result_type.
   *
   * See BoolEvaluator.hpp for an example.
   *
   * WARNING: Note that specializations of Evaluator must be placed
   *  into the namespace metaSMT.
   */
  template < typename Tag >
  struct Evaluator : public boost::mpl::false_
  {}; // evaluator
  /**@}*/
} // metaSMT
