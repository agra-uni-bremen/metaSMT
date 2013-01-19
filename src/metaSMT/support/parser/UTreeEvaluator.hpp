#pragma once 

#include "../../tags/QF_BV.hpp"
#include "../../tags/Array.hpp"
#include "../../result_wrapper.hpp"
#include "../../API/Stack.hpp"
#include "../../io/SMT2_ResultParser.hpp"

#include <boost/spirit/include/support_utree.hpp>
#include "boost/lexical_cast.hpp"
#include <boost/shared_ptr.hpp>

#include <iostream>
#include <map>
#include <stack>
#include <list>

namespace metaSMT {
namespace evaluator {

template<typename Context>
struct UTreeEvaluator
{
  enum smt2Symbol
  {
    undefined, setlogic, setoption, getoption, checksat, assertion, declarefun, getvalue, push, pop, exit
  };

  enum smt2operator
  {
    other,
    smttrue,
    smtfalse,
    smtnot,
    smteq,
    smtand,
    smtor,
    smtxor,
    smtimplies,
    smtite,
    smtbvnot,
    smtbvneg,
    smtbvand,
    smtbvnand,
    smtbvor,
    smtbvnor,
    smtbvxor,
    smtbvxnor,
    smtbvcomp,
    smtbvadd,
    smtbvmul,
    smtbvsub,
    smtbvsdiv,
    smtbvsrem,
    smtbvudiv,
    smtbvurem,
    smtbvsle,
    smtbvsge,
    smtbvslt,
    smtbvsgt,
    smtbvule,
    smtbvuge,
    smtbvult,
    smtbvugt,
    smtbvshl,
    smtbvshr,
    smtbvashr,
    smtconcat,
    smtextract,
    smtzero_extend,
    smtsign_extend
  };

  typedef std::map<std::string, smt2Symbol> SymbolMap;
  typedef std::map<std::string, smt2operator> OperatorMap;
  typedef std::map<std::string, metaSMT::logic::predicate> PredicateMap;
  typedef std::map<std::string, metaSMT::logic::QF_BV::bitvector> BitVectorMap;
  typedef typename Context::result_type result_type;
  typedef boost::spirit::utree utree;

  UTreeEvaluator(Context &ctx)
    : ctx(ctx)
    , pred_map( *boost::shared_ptr<PredicateMap>(new PredicateMap()) )
    , bv_map( *boost::shared_ptr<BitVectorMap>(new BitVectorMap()) ) {
    initialize();
  }

  UTreeEvaluator(Context &ctx,
                 PredicateMap &pred_map,
                 BitVectorMap &bv_map)
    : ctx(ctx)
    , pred_map(pred_map)
    , bv_map(bv_map) {
    initialize();
  }

  void initialize()
  {
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

    operatorMap["true"] = smttrue;
    operatorMap["false"] = smtfalse;
    operatorMap["not"] = smtnot;
    operatorMap["="] = smteq;
    operatorMap["and"] = smtand;
    operatorMap["or"] = smtor;
    operatorMap["xor"] = smtxor;
    operatorMap["=>"] = smtimplies;
    operatorMap["ite"] = smtite;
    operatorMap["bvnot"] = smtbvnot;
    operatorMap["bvneg"] = smtbvneg;
    operatorMap["bvand"] = smtbvand;
    operatorMap["bvnand"] = smtbvnand;
    operatorMap["bvor"] = smtbvor;
    operatorMap["bvnor"] = smtbvnor;
    operatorMap["bvxor"] = smtbvxor;
    operatorMap["bvxnor"] = smtbvxnor;
    operatorMap["bvcomp"] = smtbvcomp;
    operatorMap["bvadd"] = smtbvadd;
    operatorMap["bvmul"] = smtbvmul;
    operatorMap["bvsub"] = smtbvsub;
    operatorMap["bvsdiv"] = smtbvsdiv;
    operatorMap["bvsrem"] = smtbvsrem;
    operatorMap["bvudiv"] = smtbvudiv;
    operatorMap["bvurem"] = smtbvurem;
    operatorMap["bvsle"] = smtbvsle;
    operatorMap["bvsge"] = smtbvsge;
    operatorMap["bvslt"] = smtbvslt;
    operatorMap["bvsgt"] = smtbvsgt;
    operatorMap["bvule"] = smtbvule;
    operatorMap["bvuge"] = smtbvuge;
    operatorMap["bvult"] = smtbvult;
    operatorMap["bvugt"] = smtbvugt;
    operatorMap["bvshl"] = smtbvshl;
    operatorMap["bvlshr"] = smtbvshr;
    operatorMap["bvashr"] = smtbvashr;
    operatorMap["concat"] = smtconcat;
    operatorMap["extract"] = smtextract;
    operatorMap["zero_extend"] = smtzero_extend;
    operatorMap["sign_extend"] = smtsign_extend;
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
        if (metaSMT::solve(ctx)) {
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
        result_type *variable = new result_type;
        int err = getVariable(value, *variable);
        if (err == 1) {
          std::string boolvalue;
          if (metaSMT::read_value(ctx, *variable)) {
            boolvalue = "true";
          } else {
            boolvalue = "false";
          }
          std::cout << "((" << value << " " << boolvalue << "))" << std::endl;
        } else if (err == 2) {
          std::cout << "((" << value << " #b" << metaSMT::read_value(ctx, *variable) << "))" << std::endl;
        } else {
          std::cerr << "Error could not determine Variable: " << value << std::endl;
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

  result_type translateLogicalInstruction(utree tree)
  {
    result_type output;
    switch (tree.which()) {
    case boost::spirit::utree_type::list_type: {
      for (utree::iterator I = tree.begin(); I != tree.end(); ++I) {
        std::string value = utreeToString(*I);
        if (operatorMap[value] != other) {
          pushOperator(value);
        } else {
          // handle bitvector
          if (value.compare("_") == 0) {
            ++I;
            std::string bvvalue = utreeToString(*I);
            if (operatorMap[bvvalue] == smtzero_extend || operatorMap[bvvalue] == smtsign_extend) {
              pushOperator(bvvalue);
              ++I;
              int op1 = boost::lexical_cast<int>(utreeToString(*I));
              pushModBvLengthParam(op1);
            } else if (operatorMap[bvvalue] == smtextract) {
              pushOperator(bvvalue);
              ++I;
              int op1 = boost::lexical_cast<int>(utreeToString(*I));
              pushModBvLengthParam(op1);
              ++I;
              int op2 = boost::lexical_cast<int>(utreeToString(*I));
              pushModBvLengthParam(op2);
            } else {
              ++I;
              std::string bitSize = utreeToString(*I);
              pushResultType(createBvInt(bvvalue, bitSize));
            }
          } else {
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
      if (operatorMap[value] != other) {
        pushOperator(value);
        consume();
      } else {
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

  void consume()
  {
    std::string op = operatorStack.top();
    result_type result;
    switch (numOperands(op)) {
    // constants
    case 0:
      switch (operatorMap[op]) {
      case smttrue:
        result = metaSMT::evaluate(ctx, metaSMT::logic::True);
        break;
      case smtfalse:
        result = metaSMT::evaluate(ctx, metaSMT::logic::False);
        break;
      default:
        break;
      }
      break;
    // unary operators
    case 1: {
      result_type op1 = popResultType();
      switch (operatorMap[op]) {
      case smtnot:
        result = metaSMT::evaluate(ctx, metaSMT::logic::Not(op1));
        break;
      case smtbvnot:
        result = metaSMT::evaluate(ctx, metaSMT::logic::QF_BV::bvnot(op1));
        break;
      case smtbvneg:
        result = metaSMT::evaluate(ctx, metaSMT::logic::QF_BV::bvneg(op1));
        break;
      default:
        break;
      }
      break;
    }
    // binary operators
    case 2: {
      if (operatorMap[op] == smtzero_extend || operatorMap[op] == smtsign_extend) {
        int op1 = popModBvLengthParam();
        result_type op2 = popResultType();
        switch (operatorMap[op]) {
        case smtzero_extend:
          result = metaSMT::evaluate(ctx, metaSMT::logic::QF_BV::zero_extend(op1, op2));
          break;
        case smtsign_extend:
          result = metaSMT::evaluate(ctx, metaSMT::logic::QF_BV::sign_extend(op1, op2));
          break;
        default:
          assert( false && "Unreachable" );
          break;
        }
      } else {
        result_type op2 = popResultType();
        result_type op1 = popResultType();
        switch (operatorMap[op]) {
        case smteq:
          result = metaSMT::evaluate(ctx, metaSMT::logic::equal(op1, op2));
          break;
        case smtimplies:
          result = metaSMT::evaluate(ctx, metaSMT::logic::implies(op1, op2));
          break;
        case smtand:
          result = metaSMT::evaluate(ctx, metaSMT::logic::And(op1, op2));
          break;
        case smtor:
          result = metaSMT::evaluate(ctx, metaSMT::logic::Or(op1, op2));
          break;
        case smtxor:
          result = metaSMT::evaluate(ctx, metaSMT::logic::Xor(op1, op2));
          break;
        case smtbvand:
          result = metaSMT::evaluate(ctx, metaSMT::logic::QF_BV::bvand(op1, op2));
          break;
        case smtbvnand:
          result = metaSMT::evaluate(ctx, metaSMT::logic::QF_BV::bvnand(op1, op2));
          break;
        case smtbvor:
          result = metaSMT::evaluate(ctx, metaSMT::logic::QF_BV::bvor(op1, op2));
          break;
        case smtbvnor:
          result = metaSMT::evaluate(ctx, metaSMT::logic::QF_BV::bvnor(op1, op2));
          break;
        case smtbvxor:
          result = metaSMT::evaluate(ctx, metaSMT::logic::QF_BV::bvxor(op1, op2));
          break;
        case smtbvxnor:
          result = metaSMT::evaluate(ctx, metaSMT::logic::QF_BV::bvxnor(op1, op2));
          break;
        case smtbvcomp:
          result = metaSMT::evaluate(ctx, metaSMT::logic::QF_BV::bvcomp(op1, op2));
          break;
        case smtbvadd:
          result = metaSMT::evaluate(ctx, metaSMT::logic::QF_BV::bvadd(op1, op2));
          break;
        case smtbvmul:
          result = metaSMT::evaluate(ctx, metaSMT::logic::QF_BV::bvmul(op1, op2));
          break;
        case smtbvsub:
          result = metaSMT::evaluate(ctx, metaSMT::logic::QF_BV::bvsub(op1, op2));
          break;
        case smtbvsdiv:
          result = metaSMT::evaluate(ctx, metaSMT::logic::QF_BV::bvsdiv(op1, op2));
          break;
        case smtbvsrem:
          result = metaSMT::evaluate(ctx, metaSMT::logic::QF_BV::bvsrem(op1, op2));
          break;
        case smtbvudiv:
          result = metaSMT::evaluate(ctx, metaSMT::logic::QF_BV::bvudiv(op1, op2));
          break;
        case smtbvurem:
          result = metaSMT::evaluate(ctx, metaSMT::logic::QF_BV::bvurem(op1, op2));
          break;
        case smtbvsle:
          result = metaSMT::evaluate(ctx, metaSMT::logic::QF_BV::bvsle(op1, op2));
          break;
        case smtbvsge:
          result = metaSMT::evaluate(ctx, metaSMT::logic::QF_BV::bvsge(op1, op2));
          break;
        case smtbvslt:
          result = metaSMT::evaluate(ctx, metaSMT::logic::QF_BV::bvslt(op1, op2));
          break;
        case smtbvsgt:
          result = metaSMT::evaluate(ctx, metaSMT::logic::QF_BV::bvsgt(op1, op2));
          break;
        case smtbvule:
          result = metaSMT::evaluate(ctx, metaSMT::logic::QF_BV::bvule(op1, op2));
          break;
        case smtbvuge:
          result = metaSMT::evaluate(ctx, metaSMT::logic::QF_BV::bvuge(op1, op2));
          break;
        case smtbvult:
          result = metaSMT::evaluate(ctx, metaSMT::logic::QF_BV::bvult(op1, op2));
          break;
        case smtbvugt:
          result = metaSMT::evaluate(ctx, metaSMT::logic::QF_BV::bvugt(op1, op2));
          break;
        case smtbvshl:
          result = metaSMT::evaluate(ctx, metaSMT::logic::QF_BV::bvshl(op1, op2));
          break;
        case smtbvshr:
          result = metaSMT::evaluate(ctx, metaSMT::logic::QF_BV::bvshr(op1, op2));
          break;
        case smtbvashr:
          result = metaSMT::evaluate(ctx, metaSMT::logic::QF_BV::bvashr(op1, op2));
          break;
        case smtconcat:
          result = metaSMT::evaluate(ctx, metaSMT::logic::QF_BV::concat(op1, op2));
          break;
        default:
          break;
        }
      }
      break;
    }
    // ternary operators
    case 3: {
      result_type op3 = popResultType();
      switch (operatorMap[op]) {
      case smtite: {
        result_type op2 = popResultType();
        result_type op1 = popResultType();
        result = metaSMT::evaluate(ctx, metaSMT::logic::Ite(op1, op2, op3));
        break;
      }
      case smtextract: {
        int op2 = popModBvLengthParam();
        int op1 = popModBvLengthParam();
        result = metaSMT::evaluate(ctx, metaSMT::logic::QF_BV::extract(op1, op2, op3));
        break;
      }
      default:
        break;
      }
      break;
    }
    default:
      break;
    }

    neededOperandStack.pop();
    pushResultType(result);
    operatorStack.pop();
  }

  void pushOperator(std::string op)
  {
    operatorStack.push(op);
    std::pair<int, int> neededOperands(numOperands(op), 0);
    neededOperandStack.push(neededOperands);
  }

  void pushResultType(result_type op)
  {
    if (neededOperandStack.size() > 0) {
      std::pair<int, int> newTop(neededOperandStack.top().first, neededOperandStack.top().second + 1);
      neededOperandStack.pop();
      neededOperandStack.push(newTop);
    }
    resultTypeStack.push(op);
  }

  result_type popResultType()
  {
    result_type op = resultTypeStack.top();
    resultTypeStack.pop();
    return op;
  }

  void pushModBvLengthParam(int op)
  {
    if (neededOperandStack.size() > 0) {
      std::pair<int, int> newTop(neededOperandStack.top().first, neededOperandStack.top().second + 1);
      neededOperandStack.pop();
      neededOperandStack.push(newTop);
    }
    modBvLengthParamStack.push(op);
  }

  int popModBvLengthParam()
  {
    int op = modBvLengthParamStack.top();
    modBvLengthParamStack.pop();
    return op;
  }

  /* pushes constant Bit/Hex value if value begins with #b/#x
   * otherwise pushes variable if value is an identifier
   * otherwise pushes empty result_type, should crash then
   */
  void pushVarOrConstant(std::string value)
  {
    result_type variable;
    getVariable(value, variable);

    typedef std::string::const_iterator ConstIterator;
    metaSMT::io::smt2_response_grammar<ConstIterator> parser;
    ConstIterator it = value.begin(), ie = value.end();
    static boost::spirit::qi::rule< ConstIterator, unsigned long() > binary_rule
      = boost::spirit::qi::lit("#b") >> boost::spirit::qi::uint_parser<unsigned long, 2, 1, 64>()
      ;
    static boost::spirit::qi::rule< ConstIterator, unsigned long() > hex_rule
      = boost::spirit::qi::lit("#x") >> boost::spirit::qi::uint_parser<unsigned long, 16, 1, 16>()
      ;

    unsigned long number;
    it = value.begin(), ie = value.end();
    if ( boost::spirit::qi::parse(it, ie, binary_rule, number) ) {
      assert( it == ie && "Expression not completely consumed" );
      value.erase(0, 2);
      variable = metaSMT::evaluate(ctx, metaSMT::logic::QF_BV::bvbin(value));
    }

    it = value.begin(), ie = value.end();
    if ( boost::spirit::qi::parse(it, ie, hex_rule, number) ) {
      assert( it == ie && "Expression not completely consumed" );
      value.erase(0, 2);
      variable = metaSMT::evaluate(ctx, metaSMT::logic::QF_BV::bvhex(value));
    }
    pushResultType(variable);
  }

  result_type createBvInt(std::string value, std::string bitSize)
  {
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
        return metaSMT::evaluate(ctx, metaSMT::logic::QF_BV::bit1);
      } else if (number == 0) {
        return metaSMT::evaluate(ctx, metaSMT::logic::QF_BV::bit0);
      }
    }
    return metaSMT::evaluate(ctx, metaSMT::logic::QF_BV::bvsint(number, width));
  }

  void translateDeclareFunction(utree function)
  {
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
      unsigned width = boost::lexical_cast<unsigned>(bitSize);
      bv_map[functionName] = metaSMT::logic::QF_BV::new_bitvector(width);
      break;
    }
    case boost::spirit::utree_type::string_type: {
      pred_map[functionName] = metaSMT::logic::new_variable();
      break;
    }
    default:
      break;
    }
  }

  int getVariable(std::string name, result_type &result) {
    // name is a variable identifier, therfore unique and may only be in one map
    PredicateMap::iterator pred_it = pred_map.find(name);
    if (pred_it != pred_map.end()) {
      result = metaSMT::evaluate(ctx, pred_it->second);
      return 1;
    }

    BitVectorMap::iterator bv_it = bv_map.find(name);
    if (bv_it != bv_map.end()) {
      result = metaSMT::evaluate(ctx, bv_it->second);
      return 2;
    }

    return -1;
  }

  int numOperands(std::string op)
  {
    switch (operatorMap[op]) {
    case smttrue:
    case smtfalse:
      return 0;
    case smtnot:
    case smtbvnot:
    case smtbvneg:
      return 1;
    case smteq:
    case smtand:
    case smtor:
    case smtxor:
    case smtimplies:
    case smtbvand:
    case smtbvnand:
    case smtbvor:
    case smtbvnor:
    case smtbvxor:
    case smtbvxnor:
    case smtbvcomp:
    case smtbvadd:
    case smtbvmul:
    case smtbvsub:
    case smtbvsdiv:
    case smtbvsrem:
    case smtbvudiv:
    case smtbvurem:
    case smtbvsle:
    case smtbvsge:
    case smtbvslt:
    case smtbvsgt:
    case smtbvule:
    case smtbvuge:
    case smtbvult:
    case smtbvugt:
    case smtbvshl:
    case smtbvshr:
    case smtbvashr:
    case smtconcat:
    case smtzero_extend:
    case smtsign_extend:
      return 2;
    case smtite:
    case smtextract:
      return 3;
    case other:
    default:
      break;
    }
    return 0;
  }

  bool canConsume()
  {
    if (!operatorStack.empty()) {
      if (neededOperandStack.top().first == neededOperandStack.top().second) {
        return true;
      }
    }
    return false;
  }

  std::string utreeToString(utree tree)
  {
    std::stringstream stringStream;
    stringStream << tree;
    std::string output = stringStream.str();
    size_t found = output.find("\"");
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
  Context& ctx;
  SymbolMap symbolMap;
  OperatorMap operatorMap;

  std::stack<std::string> operatorStack;
  std::stack<int> modBvLengthParamStack;
  std::stack<std::pair<int, int> > neededOperandStack;

  PredicateMap &pred_map;
  BitVectorMap &bv_map;
  std::stack<result_type> resultTypeStack;
  std::list<bool> results;
}; // UTreeEvaluator
}// namespace evaluator
} // namespace metaSMT
