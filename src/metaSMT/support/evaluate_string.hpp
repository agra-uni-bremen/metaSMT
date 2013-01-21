#pragma once
#include "parser/UTreeEvaluator.hpp"
#include "parser/SMT2Parser.hpp"
#include <boost/shared_ptr.hpp>
#include <sstream>

namespace metaSMT {
  template < typename Context >
  typename Context::result_type
  evaluate_string( Context &ctx, std::string const &formula) {
    typedef evaluator::UTreeEvaluator< Context > Evaluator;
    Evaluator evaluator(ctx);

    std::stringstream ss;
    ss << formula;

    boost::spirit::utree::list_type ast;
    smt2::SMT2Parser<Evaluator> parser(evaluator);
    bool const success = parser.parse(ss, ast);
    assert( success && "Parsing failed" );

    return evaluator.evaluateExpressions(ast);
  }

  template < typename Context >
  typename Context::result_type
  evaluate_string( Context &ctx,
                   std::string const &formula,
                   std::map<std::string,
                   boost::shared_ptr< type::TypedSymbol<Context> > > &var_map) {
    typedef evaluator::UTreeEvaluator< Context > Evaluator;
    Evaluator evaluator(ctx, var_map);

    std::stringstream ss;
    ss << formula;

    boost::spirit::utree::list_type ast;
    smt2::SMT2Parser<Evaluator> parser(evaluator);
    bool const success = parser.parse(ss, ast);
    assert( success && "Parsing failed" );

    return evaluator.evaluateExpressions(ast);
  }
} // metaSMT
