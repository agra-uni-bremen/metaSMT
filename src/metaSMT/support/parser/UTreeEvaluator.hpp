#pragma once 

#include "../../tags/QF_BV.hpp"
#include "../../result_wrapper.hpp"
#include "../../API/Stack.hpp"
#include "../../io/SMT2_ResultParser.hpp"
#include "../../support/SMT_Tag_Mapping.hpp"
#include "../../support/index/Logics.hpp"
#include "../../types/TypedSymbol.hpp"

#include <boost/spirit/include/support_utree.hpp>
#include <boost/lexical_cast.hpp>
#include <boost/shared_ptr.hpp>
#include <boost/optional.hpp>
#include <boost/mpl/string.hpp>
#include <boost/mpl/for_each.hpp>

#include <iostream>
#include <map>
#include <stack>
#include <list>

namespace metaSMT {
  namespace evaluator {
    namespace QF_BV = metaSMT::logic::QF_BV;
    namespace mpl = boost::mpl;

    namespace detail {
      struct IndexVisitor {
        IndexVisitor(bool &found,
                     logic::index &idx,
                     std::string const &name)
          : found(found)
          , idx(idx)
          , name(name)
        {}

        template < typename Pair >
        void operator()( Pair const & ) {
          typedef typename Pair::first Tag;
          typedef typename Pair::second Name;
          if ( !found &&
               mpl::c_str<Name>::value == name ) {          
            found = true;
            idx = logic::Index<Tag>::value;
          }
        }

        bool &found;
        logic::index &idx;
        std::string const name;
      }; // IndexVisitor
    } // detail

    template < typename NameMap >
    inline boost::optional< logic::index >
    get_index( std::string const &name ) {
      bool found = false;
      logic::index idx = 0;
      detail::IndexVisitor visitor(found, idx, name);
      mpl::for_each< NameMap >( visitor );
      if ( found ) {
        return boost::optional< logic::index >(idx);
      }
      else {
        return boost::optional< logic::index >();
      }
    }

template<typename Context>
struct UTreeEvaluator
{
  enum smt2Symbol
  {
    undefined, setlogic, setoption, getoption, checksat, assertion, declarefun, getvalue, push, pop, exit
  };

  typedef std::map<std::string, smt2Symbol> SymbolMap;
  typedef type::TypedSymbol<Context> TypedSymbol;
  typedef boost::shared_ptr< TypedSymbol > TypedSymbolPtr;
  typedef std::map<std::string, TypedSymbolPtr > VarMap;
  typedef typename Context::result_type result_type;
  typedef boost::spirit::utree utree;

  UTreeEvaluator(Context &ctx)
    : ctx(ctx)
    , var_map_ptr(new VarMap())
    , var_map(*var_map_ptr) {
    initialize();
  }

  UTreeEvaluator(Context &ctx,
                 VarMap &var_map)
    : ctx(ctx)
    , var_map(var_map) {
    initialize();
  }

  void initialize() {
    symbolMap["set-logic"] = setlogic;
    symbolMap["set-option"] = setoption;
    symbolMap["get-option"] = getoption;
    symbolMap["check-sat"] = checksat;
    symbolMap["assertion"] = assertion;
    symbolMap["assert"] = assertion;
    symbolMap["declare-fun"] = declarefun;
    symbolMap["get-value"] = getvalue;
    symbolMap["push"] = push;
    symbolMap["pop"] = pop;
    symbolMap["exit"] = exit;
  }

  result_type evaluateExpressions(utree ast) {
    result_type r = evaluate( ctx, logic::True );
    for ( utree::iterator it = ast.begin(), ie = ast.end();
          it != ie; ++it ) {
      utree command = *it;
      utree::iterator utree_it = command.begin();
      std::string const symbol_string = utreeToString(*utree_it);
      switch (symbolMap[symbol_string]) {
      case assertion:
        ++utree_it;
        r = evaluate(ctx, And(r, translateLogicalInstruction(*utree_it)));
        break;
      case declarefun:
        translateDeclareFunction(command);
        break;
      default:
        assert( false && "Unsupported" );
      }
    }
    return r;
  }

  void evaluateInstance(utree ast) {
    for (utree::iterator I = ast.begin(); I != ast.end(); ++I) {
      utree command = *I;
      utree::iterator commandIterator = command.begin();
      utree symbol = *commandIterator;
      std::string symbolString = utreeToString(symbol);

      switch (symbolMap[symbolString]) {
      case push: {
        ++commandIterator;
        std::string pushValue = utreeToString(*commandIterator);
        unsigned howmany = boost::lexical_cast<unsigned>(pushValue);
        metaSMT::push(ctx, howmany);
        break;
      }
      case checksat: {
        if (solve(ctx)) {
          std::cout << "sat" << std::endl;
        } else {
          std::cout << "unsat" << std::endl;
        }
        break;
      }
      case assertion: {
        ++commandIterator;
        utree logicalInstruction = *commandIterator;
        metaSMT::assertion(ctx, translateLogicalInstruction(logicalInstruction));
        break;
      }
      case declarefun:
        translateDeclareFunction(command);
        break;
      case pop: {
        ++commandIterator;
        std::string popValue = utreeToString(*commandIterator);
        unsigned howmany = boost::lexical_cast<unsigned>(popValue);
        metaSMT::pop(ctx, howmany);
        break;
      }
      case getvalue: {
        ++commandIterator;
        std::string value = utreeToString(*commandIterator);
        boost::optional<TypedSymbolPtr> var = getVariable(value);
        if ( var ) {
          if ( (*var)->isBool() ) {
            bool b = read_value(ctx, (*var)->eval(ctx));
            std::cout << "((" << value << " " << (b ? "true" : "false") << "))" << '\n';
          }
          else if ( (*var)->isBitVector() ) {
            std::cout << "((" << value << " #b" << read_value(ctx, (*var)->eval(ctx)) << "))" << '\n';
          }
          else {
            assert( false && "Variable type is not supported" );
          }
        }
        else {
          // std::cerr << "[DBG] Variable: " << value << '\n';
          assert( false && "Could not determine variable ");
        }
        break;
      }
      case undefined:
        std::cerr << "Error could not determine Symbol: " << symbolString << std::endl;
        break;
      case setoption:
      case getoption:
      case setlogic:
      case exit:
      default:
        break;
      }
    }
  }

  result_type translateLogicalInstruction(utree tree) {
    result_type output;
    switch (tree.which()) {
    case boost::spirit::utree_type::list_type: {
      for (utree::iterator I = tree.begin(); I != tree.end(); ++I) {
        std::string value = utreeToString(*I);
        boost::optional< logic::index > idx = get_index<SMT_NameMap>(value);
        if ( idx ) {
          pushOperator(value);
        }
        else {
          // handle bitvector
          if (value.compare("_") == 0) {
            ++I;
            std::string bvvalue = utreeToString(*I);
            boost::optional< logic::index > idx = get_index<SMT_NameMap>(bvvalue);
            if ( !idx ) {
              ++I;
              std::string bitSize = utreeToString(*I);
              pushResultType(createBvInt(bvvalue, bitSize));
            }
            else if ( *idx == logic::Index<bvtags::zero_extend_tag>::value ||
                      *idx == logic::Index<bvtags::sign_extend_tag>::value ) {
              pushOperator(bvvalue);
              ++I;
              int op1 = boost::lexical_cast<int>(utreeToString(*I));
              pushModBvLengthParam(op1);
            }
            else if ( *idx == logic::Index<bvtags::extract_tag>::value ) {
              pushOperator(bvvalue);
              ++I;
              int op1 = boost::lexical_cast<int>(utreeToString(*I));
              pushModBvLengthParam(op1);
              ++I;
              int op2 = boost::lexical_cast<int>(utreeToString(*I));
              pushModBvLengthParam(op2);
            }
          }
          else {
            pushVarOrConstant(value);
          }
        }

        while (canConsume()) {
          consume();
        }
      }
      break;
    }
    case boost::spirit::utree_type::string_type: {
      std::string value = utreeToString(tree);
      boost::optional< logic::index > idx = get_index<SMT_NameMap>(value);
      if ( idx ) {
        pushOperator(value);
        consume();
      }
      else {
        pushVarOrConstant(value);
      }
      break;
    }
    default:
      break;
    }

    if (resultTypeStack.size() != 1) {
      std::cerr << "wrong stack size:" << resultTypeStack.size() << " stack size should be 1" << std::endl;
    }
    output = resultTypeStack.top();
    resultTypeStack.pop();
    return output;
  }

  void consume() {
    std::string op = operatorStack.top();
    result_type result;
    switch (numOperands(op)) {
    // constants
    case 0: {
      boost::optional< logic::index > idx = get_index<SMT_NameMap>(op);
      assert( idx );
      switch ( *idx ) {
      case logic::Index<predtags::true_tag>::value :
        result = evaluate(ctx, logic::True);
        break;
      case logic::Index<predtags::false_tag>::value :
        result = evaluate(ctx, logic::False);
        break;
      default:
        assert( false );
        break;
      }
      break;
    }
    // unary operators
    case 1: {
      result_type op1 = popResultType();
      boost::optional< logic::index > idx = get_index<SMT_NameMap>(op);
      assert( idx );
      switch ( *idx ) {
      case logic::Index<predtags::not_tag>::value :
        result = evaluate(ctx, logic::Not(op1));
        break;
      case logic::Index<bvtags::bvnot_tag>::value :
        result = evaluate(ctx, QF_BV::bvnot(op1));
        break;
      case logic::Index<bvtags::bvneg_tag>::value :
        result = evaluate(ctx, QF_BV::bvneg(op1));
        break;
      default:
        assert( false );
        break;
      }
      break;
    }
    // binary operators
    case 2: {
      boost::optional< logic::index > idx = get_index<SMT_NameMap>(op);
      assert( idx );
      if ( *idx == logic::Index<bvtags::zero_extend_tag>::value ||
           *idx == logic::Index<bvtags::sign_extend_tag>::value ) {
        int op1 = popModBvLengthParam();
        result_type op2 = popResultType();
        switch ( *idx ) {
        case logic::Index<bvtags::zero_extend_tag>::value :
          result = evaluate(ctx, QF_BV::zero_extend(op1, op2));
          break;
        case logic::Index<bvtags::sign_extend_tag>::value :
          result = evaluate(ctx, QF_BV::sign_extend(op1, op2));
          break;
        default:
          assert( false && "Unreachable" );
          break;
        }
      }
      else {
        result_type op2 = popResultType();
        result_type op1 = popResultType();
        switch ( *idx ) {
        case logic::Index<predtags::equal_tag>::value :
          result = evaluate(ctx, logic::equal(op1, op2));
          break;
        case logic::Index<predtags::implies_tag>::value :
          result = evaluate(ctx, logic::implies(op1, op2));
          break;
        case logic::Index<predtags::and_tag>::value:
          result = evaluate(ctx, logic::And(op1, op2));
          break;
        case logic::Index<predtags::or_tag>::value:
          result = evaluate(ctx, logic::Or(op1, op2));
          break;
        case logic::Index<predtags::xor_tag>::value:
          result = evaluate(ctx, logic::Xor(op1, op2));
          break;
        case logic::Index<bvtags::bvand_tag>::value:
          result = evaluate(ctx, QF_BV::bvand(op1, op2));
          break;
        case logic::Index<bvtags::bvnand_tag>::value:
          result = evaluate(ctx, QF_BV::bvnand(op1, op2));
          break;
        case logic::Index<bvtags::bvor_tag>::value:
          result = evaluate(ctx, QF_BV::bvor(op1, op2));
          break;
        case logic::Index<bvtags::bvnor_tag>::value:
          result = evaluate(ctx, QF_BV::bvnor(op1, op2));
          break;
        case logic::Index<bvtags::bvxor_tag>::value:
          result = evaluate(ctx, QF_BV::bvxor(op1, op2));
          break;
        case logic::Index<bvtags::bvxnor_tag>::value:
          result = evaluate(ctx, QF_BV::bvxnor(op1, op2));
          break;
        case logic::Index<bvtags::bvcomp_tag>::value:
          result = evaluate(ctx, QF_BV::bvcomp(op1, op2));
          break;
        case logic::Index<bvtags::bvadd_tag>::value:
          result = evaluate(ctx, QF_BV::bvadd(op1, op2));
          break;
        case logic::Index<bvtags::bvmul_tag>::value:
          result = evaluate(ctx, QF_BV::bvmul(op1, op2));
          break;
        case logic::Index<bvtags::bvsub_tag>::value:
          result = evaluate(ctx, QF_BV::bvsub(op1, op2));
          break;
        case logic::Index<bvtags::bvsdiv_tag>::value:
          result = evaluate(ctx, QF_BV::bvsdiv(op1, op2));
          break;
        case logic::Index<bvtags::bvsrem_tag>::value:
          result = evaluate(ctx, QF_BV::bvsrem(op1, op2));
          break;
        case logic::Index<bvtags::bvudiv_tag>::value:
          result = evaluate(ctx, QF_BV::bvudiv(op1, op2));
          break;
        case logic::Index<bvtags::bvurem_tag>::value:
          result = evaluate(ctx, QF_BV::bvurem(op1, op2));
          break;
        case logic::Index<bvtags::bvsle_tag>::value:
          result = evaluate(ctx, QF_BV::bvsle(op1, op2));
          break;
        case logic::Index<bvtags::bvsge_tag>::value:
          result = evaluate(ctx, QF_BV::bvsge(op1, op2));
          break;
        case logic::Index<bvtags::bvslt_tag>::value:
          result = evaluate(ctx, QF_BV::bvslt(op1, op2));
          break;
        case logic::Index<bvtags::bvsgt_tag>::value:
          result = evaluate(ctx, QF_BV::bvsgt(op1, op2));
          break;
        case logic::Index<bvtags::bvule_tag>::value:
          result = evaluate(ctx, QF_BV::bvule(op1, op2));
          break;
        case logic::Index<bvtags::bvuge_tag>::value:
          result = evaluate(ctx, QF_BV::bvuge(op1, op2));
          break;
        case logic::Index<bvtags::bvult_tag>::value:
          result = evaluate(ctx, QF_BV::bvult(op1, op2));
          break;
        case logic::Index<bvtags::bvugt_tag>::value:
          result = evaluate(ctx, QF_BV::bvugt(op1, op2));
          break;
        case logic::Index<bvtags::bvshl_tag>::value:
          result = evaluate(ctx, QF_BV::bvshl(op1, op2));
          break;
        case logic::Index<bvtags::bvshr_tag>::value:
          result = evaluate(ctx, QF_BV::bvshr(op1, op2));
          break;
        case logic::Index<bvtags::bvashr_tag>::value:
          result = evaluate(ctx, QF_BV::bvashr(op1, op2));
          break;
        case logic::Index<bvtags::concat_tag>::value:
          result = evaluate(ctx, QF_BV::concat(op1, op2));
          break;
        default:
          assert( false );
          break;
        }
      }
      break;
    }
    // ternary operators
    case 3: {
      result_type op3 = popResultType();
      boost::optional< logic::index > idx = get_index<SMT_NameMap>(op);
      assert( idx );
      switch ( *idx ) {
      case logic::Index<predtags::ite_tag>::value: {
        result_type op2 = popResultType();
        result_type op1 = popResultType();
        result = evaluate(ctx, logic::Ite(op1, op2, op3));
        break;
      }
      case logic::Index<bvtags::extract_tag>::value: {
        int op2 = popModBvLengthParam();
        int op1 = popModBvLengthParam();
        result = evaluate(ctx, QF_BV::extract(op1, op2, op3));
        break;
      }
      default:
        assert( false );
        break;
      }
      break;
    }
    default:
      assert( false );
      break;
    }

    neededOperandStack.pop();
    pushResultType(result);
    operatorStack.pop();
  }

  void pushOperator(std::string op) {
    operatorStack.push(op);
    std::pair<int, int> neededOperands(numOperands(op), 0);
    neededOperandStack.push(neededOperands);
  }

  void pushResultType(result_type op) {
    if (neededOperandStack.size() > 0) {
      std::pair<int, int> newTop(neededOperandStack.top().first, neededOperandStack.top().second + 1);
      neededOperandStack.pop();
      neededOperandStack.push(newTop);
    }
    resultTypeStack.push(op);
  }

  result_type popResultType() {
    result_type op = resultTypeStack.top();
    resultTypeStack.pop();
    return op;
  }

  void pushModBvLengthParam(int op) {
    if (neededOperandStack.size() > 0) {
      std::pair<int, int> newTop(neededOperandStack.top().first, neededOperandStack.top().second + 1);
      neededOperandStack.pop();
      neededOperandStack.push(newTop);
    }
    modBvLengthParamStack.push(op);
  }

  int popModBvLengthParam() {
    int op = modBvLengthParamStack.top();
    modBvLengthParamStack.pop();
    return op;
  }

  /* pushes constant Bit/Hex value if value begins with #b/#x
   * otherwise pushes variable if value is an identifier
   * otherwise pushes empty result_type, should crash then
   */
  void pushVarOrConstant(std::string value) {
    boost::optional<TypedSymbolPtr> var = getVariable(value);
    if ( var ) {
      pushResultType((*var)->eval(ctx));
      return;
    }

    typedef std::string::const_iterator ConstIterator;
    io::smt2_response_grammar<ConstIterator> parser;
    ConstIterator it = value.begin(), ie = value.end();
    static boost::spirit::qi::rule< ConstIterator, unsigned long() > binary_rule
      = boost::spirit::qi::lit("#b") >> boost::spirit::qi::uint_parser<unsigned long, 2, 1, 64>()
      ;
    static boost::spirit::qi::rule< ConstIterator, unsigned long() > hex_rule
      = boost::spirit::qi::lit("#x") >> boost::spirit::qi::uint_parser<unsigned long, 16, 1, 16>()
      ;

    result_type result;
    unsigned long number;
    it = value.begin(), ie = value.end();
    if ( boost::spirit::qi::parse(it, ie, binary_rule, number) ) {
      assert( it == ie && "Expression not completely consumed" );
      value.erase(0, 2);
      result = evaluate(ctx, QF_BV::bvbin(value));
    }

    it = value.begin(), ie = value.end();
    if ( boost::spirit::qi::parse(it, ie, hex_rule, number) ) {
      assert( it == ie && "Expression not completely consumed" );
      value.erase(0, 2);
      result = evaluate(ctx, QF_BV::bvhex(value));
    }

    pushResultType(result);
  }

  result_type createBvInt(std::string value, std::string bitSize) const {
    unsigned long number = 0;
    if (value.size() > 2) {
      if (value.find("bv", 0, 2) != value.npos) {
        value.erase(0, 2);
        number = boost::lexical_cast<unsigned long>(value);
      }
    }
    unsigned width = boost::lexical_cast<unsigned>(bitSize);
    if (width == 1) {
      if (number == 1) {
        return evaluate(ctx, QF_BV::bit1);
      } else if (number == 0) {
        return evaluate(ctx, QF_BV::bit0);
      }
    }
    return evaluate(ctx, QF_BV::bvsint(number, width));
  }

  void translateDeclareFunction(utree function) {
    utree::iterator functionIterator = function.begin();
    ++functionIterator;
    std::string functionName = utreeToString(*functionIterator);
    ++functionIterator;
    ++functionIterator;
    utree functionType = *functionIterator;

    switch (functionType.which()) {
    case boost::spirit::utree_type::list_type: {
      utree::iterator bitVecIterator = functionType.begin();
      ++bitVecIterator;
      ++bitVecIterator;
      std::string bitSize = utreeToString(*bitVecIterator);
      unsigned const w = boost::lexical_cast<unsigned>(bitSize);
      var_map[functionName] = TypedSymbolPtr(new TypedSymbol(QF_BV::new_bitvector(w), w));
      break;
    }
    case boost::spirit::utree_type::string_type: {
      var_map[functionName] = TypedSymbolPtr(new TypedSymbol(logic::new_variable()));
      break;
    }
    default:
      break;
    }
  }

  boost::optional<TypedSymbolPtr>
  getVariable( std::string const &name ) const {
    typename VarMap::const_iterator it = var_map.find(name);
    if (it != var_map.end()) {
      return boost::optional<TypedSymbolPtr>(it->second);
    }
    else {
      return boost::optional<TypedSymbolPtr>();
    }
  }

  unsigned char numOperands(std::string const op) const {
    boost::optional< logic::index > const idx = get_index<SMT_NameMap>(op);
    assert( idx );
    switch ( *idx ) {
    case logic::Index<predtags::true_tag>::value:
    case logic::Index<predtags::false_tag>::value:
      return 0;
    case logic::Index<predtags::not_tag>::value:
    case logic::Index<bvtags::bvnot_tag>::value:
    case logic::Index<bvtags::bvneg_tag>::value:
      return 1;
    case logic::Index<predtags::equal_tag>::value:
    case logic::Index<predtags::and_tag>::value:
    case logic::Index<predtags::or_tag>::value:
    case logic::Index<predtags::xor_tag>::value:
    case logic::Index<predtags::implies_tag>::value:
    case logic::Index<bvtags::bvand_tag>::value:
    case logic::Index<bvtags::bvnand_tag>::value:
    case logic::Index<bvtags::bvor_tag>::value:
    case logic::Index<bvtags::bvnor_tag>::value:
    case logic::Index<bvtags::bvxor_tag>::value:
    case logic::Index<bvtags::bvxnor_tag>::value:
    case logic::Index<bvtags::bvcomp_tag>::value:
    case logic::Index<bvtags::bvadd_tag>::value:
    case logic::Index<bvtags::bvmul_tag>::value:
    case logic::Index<bvtags::bvsub_tag>::value:
    case logic::Index<bvtags::bvsdiv_tag>::value:
    case logic::Index<bvtags::bvsrem_tag>::value:
    case logic::Index<bvtags::bvudiv_tag>::value:
    case logic::Index<bvtags::bvurem_tag>::value:
    case logic::Index<bvtags::bvsle_tag>::value:
    case logic::Index<bvtags::bvsge_tag>::value:
    case logic::Index<bvtags::bvslt_tag>::value:
    case logic::Index<bvtags::bvsgt_tag>::value:
    case logic::Index<bvtags::bvule_tag>::value:
    case logic::Index<bvtags::bvuge_tag>::value:
    case logic::Index<bvtags::bvult_tag>::value:
    case logic::Index<bvtags::bvugt_tag>::value:
    case logic::Index<bvtags::bvshl_tag>::value:
    case logic::Index<bvtags::bvshr_tag>::value:
    case logic::Index<bvtags::bvashr_tag>::value:
    case logic::Index<bvtags::concat_tag>::value:
    case logic::Index<bvtags::zero_extend_tag>::value:
    case logic::Index<bvtags::sign_extend_tag>::value:
      return 2;
    case logic::Index<predtags::ite_tag>::value:
    case logic::Index<bvtags::extract_tag>::value:
      return 3;
    default:
      assert( false );
      break;
    }
    return 0;
  }

  bool canConsume() const {
    if ( operatorStack.empty() )
      return false;

    return (neededOperandStack.top().first == neededOperandStack.top().second);
  }

  std::string utreeToString(utree const tree) const {
    std::stringstream ss;
    ss << tree;
    std::string output = ss.str();
    std::size_t found = output.find("\"");
    while (found != output.npos) {
      output.erase(found, 1);
      found = output.find("\"");
    }
    found = output.find(" ");
    while (found != output.npos) {
      output.erase(found, 1);
      found = output.find(" ");
    }
    found = output.find("(");
    while (found != output.npos) {
      output.erase(found, 1);
      found = output.find("(");
    }
    found = output.find(")");
    while (found != output.npos) {
      output.erase(found, 1);
      found = output.find(")");
    }
    return output;
  }

protected:
  Context &ctx;
  SymbolMap symbolMap;

  std::stack<std::string> operatorStack;
  std::stack<int> modBvLengthParamStack;
  std::stack<std::pair<int, int> > neededOperandStack;

  boost::shared_ptr<VarMap> var_map_ptr;
  VarMap &var_map;
  std::stack<result_type> resultTypeStack;
  std::list<bool> results;
}; // UTreeEvaluator
}// namespace evaluator
} // namespace metaSMT
