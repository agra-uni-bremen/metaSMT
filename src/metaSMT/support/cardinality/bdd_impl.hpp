#pragma once

#include "object.hpp"

#include <metaSMT/frontend/Logic.hpp>

#include <boost/mpl/assert.hpp>
#include <boost/mpl/contains.hpp>

namespace metaSMT {
  namespace cardinality {
    namespace bdd {
      /**
       * Generalized cardinality constraint based on a construction
       * using Binary Decision Diagrams (BDD) by E&eacute;n and
       * S&ouml;rensson [1] and Bailleux et al. [2].
       *
       * [1] N. E&eacute;n and N. S&ouml;rensson. Translating
       * pseudo-boolean constraints into SAT.  In Journal on
       * Satisfiability, Boolean Modeling and Computation, volume 2,
       * pages 1-26, 2006.
       *
       * [2] O. Bailleux, Y. Boufkhad, and O. Roussel, A Translation of
       * Pseudo-Boolean Constraints to SAT, Journal on Satisfiability,
       * Boolean Modeling and Computation, volume 2, pages 191-200, 2006.
       *
       * The tableau algorithm keeps only two rows of the tableau in
       * memory which we call ``rails''.
       *
       * The construction applies to all operator types (<, <=, =, >=, >).
       * An operator is selected by assigning values to the arguments lt,
       * eq, gt, e.g., the less equal operator corresponds to lt = True,
       * eq = True, gt = False.
       *
       * For instance, the constraint
       *
       *    ps[0] + ps[1] + ps[2] + ps[3] <=> 3 with <=> in {<, >, =, <=, >=}
       *
       * corresponds to the following tableau
       *       RAILS  |   0    1     2     3
       *              |          lt    lt    lt
       *     ---------|------------------------
       *        0     |    eq ps[0] ps[1] ps[2]
       *        1  gt | ps[0] ps[1] ps[2] ps[3]
       *
       * From the bottom right node of the tableau a logic formula is
       * constructed using the ITE-operator where the left neighbor node
       * and the top neighbor node serve as the then and else part,
       * respectively.
       *
       * Moreover, notice that cells with entries lt and gt are not
       * explicitly saved in rails but are directly encoded when the
       * formula is created.
       *
       * Precondition: ps.size > 0 && cardinality > 0 && ps.size() > cardinality
       */
       template <typename Context, typename Boolean, typename LT_Expr, typename EQ_Expr, typename GT_Expr>
       typename Context::result_type
       cardinality_any(Context &ctx, std::vector<Boolean> const &ps, unsigned cardinality,
                         LT_Expr lt, EQ_Expr eq, GT_Expr gt) {
         using namespace metaSMT::logic;
         assert(ps.size() > 0 && "Cardinality constraint requires at least one input variable");
         assert(cardinality > 0 && "Unsatisfied precondition for tableau construction");

         assert( ps.size() > cardinality );

         unsigned const rail_size = cardinality+1;
         std::vector<typename Context::result_type> rails[2];
        rails[0].resize(rail_size);
        rails[1].resize(rail_size);

        // Tableau algorithm - Iteratively calculate all elements
        for (unsigned v = 0; v < ps.size() - cardinality + 1; ++v) {
          for (unsigned u = 0; u < cardinality + 1; ++u) {
            if (u == 0 && v == 0) {
              rails[0][0] = evaluate(ctx, eq);
            } else if (u == 0) {
              rails[v%2][0] = evaluate(ctx, Ite(evaluate(ctx, ps[v-1]), gt, rails[(v-1)%2][0]));
            } else if (v == 0) {
              rails[0][u] = evaluate(ctx, Ite(evaluate(ctx, ps[u-1]), rails[0][u-1], lt));
            } else {
              rails[v%2][u] = evaluate(ctx, Ite(ps[u+v-1], rails[v%2][u-1], rails[(v-1)%2][u]));
            }
          }
        }
        return rails[(ps.size() - cardinality)%2][cardinality];
      }

      template < typename Context, typename Tag, typename Boolean >
      typename Context::result_type
      cardinality(Context &ctx, cardinality::Cardinality< Tag, Boolean > const &c) {
        /** error: unknown tag **/
        typedef boost::mpl::vector< tag::eq_tag, tag::lt_tag, tag::leq_tag, tag::geq_tag, tag::gt_tag > AllTags;
        BOOST_MPL_ASSERT_NOT( (boost::mpl::contains<AllTags, Tag>) );
      }

      template < typename Context, typename Boolean >
      typename Context::result_type
      cardinality(Context &ctx, cardinality::Cardinality<tag::eq_tag, Boolean> const &c) {
        std::vector<Boolean> const &ps = c.ps;
        unsigned const cardinality = c.cardinality;

        assert(ps.size() > 0 && "Equality cardinality constraint requires at least one input variable");

        if (cardinality == 0) {
          typename Context::result_type res = evaluate(ctx, logic::True);
          for (unsigned u = 0; u < ps.size(); ++u)
            res = evaluate(ctx, logic::And(res, logic::Not(ps[u])));
          return res;
        }

        if (ps.size() == cardinality) {
          typename Context::result_type res = evaluate(ctx, logic::True);
          for (unsigned u = 0; u < ps.size(); ++u)
            res = evaluate(ctx, logic::And(res, ps[u]));
          return res;
        }

        return cardinality_any(ctx, ps, cardinality, logic::False, logic::True, logic::False);
      }

      template < typename Context, typename Boolean >
      typename Context::result_type
      cardinality(Context &ctx, cardinality::Cardinality<tag::lt_tag, Boolean> const &c) {
        std::vector<Boolean> const &ps = c.ps;
        unsigned const cardinality = c.cardinality;

        assert(ps.size() > 0 && "Lower than cardinality constraint requires at least one input variable");
        return evaluate(ctx, Not(cardinality_geq(ctx, ps, cardinality)));
      }

      template < typename Context, typename Boolean >
      typename Context::result_type
      cardinality(Context &ctx, cardinality::Cardinality<tag::leq_tag, Boolean> const &c) {
        std::vector<Boolean> const &ps = c.ps;
        unsigned const cardinality = c.cardinality;

        assert(ps.size() > 0 && "Lower equal cardinality constraint requires at least one input variable");

        if (ps.size() < cardinality) {
          return evaluate(ctx, logic::True);
        }

        if (ps.size() == cardinality) {
          return evaluate(ctx, logic::True);
        }

        if (cardinality == 0) {
          typename Context::result_type res = evaluate(ctx, logic::True);
          for (unsigned u = 0; u < ps.size(); ++u)
            res = evaluate(ctx, And(res, Not(ps[u])));
          return res;
        }

        return cardinality_any(ctx, ps, cardinality, logic::True, logic::True, logic::False);
      }

      template < typename Context, typename Boolean >
      typename Context::result_type
      cardinality(Context &ctx, cardinality::Cardinality<tag::geq_tag, Boolean> const &c) {
        std::vector<Boolean> const &ps = c.ps;
        unsigned const cardinality = c.cardinality;

        assert(ps.size() > 0 && "Greater equal cardinality constraint requires at least one input variable");

        if (ps.size() < cardinality) {
          return evaluate(ctx, logic::False);
        }

        if (cardinality == 0) {
          return evaluate(ctx, logic::True);
        }

        if (ps.size() == cardinality) {
          typename Context::result_type res = evaluate(ctx, logic::True);
          for (unsigned u = 0; u < ps.size(); ++u)
            res = evaluate(ctx, And(res, ps[u]));
          return res;
        }

        return cardinality_any(ctx, ps, cardinality, logic::False, logic::True, logic::True);
      }

      template < typename Context, typename Boolean >
      typename Context::result_type
      cardinality(Context &ctx, cardinality::Cardinality<tag::gt_tag, Boolean> const &c) {
        std::vector<Boolean> const &ps = c.ps;
        unsigned const cardinality = c.cardinality;

        assert(ps.size() > 0 && "Greater than cardinality constraint requires at least one input variable");
        return evaluate(ctx, Not(cardinality_leq(ctx, ps, cardinality)));
      }
    } // bdd
  } // cardinality
} // metaSMT
