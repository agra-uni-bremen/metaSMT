#pragma once 

#include "../../tags/QF_BV.hpp"
#include "../../tags/Array.hpp"
#include "../../result_wrapper.hpp"
#include "../../API/Stack.hpp"

#include <iostream>
#include <map>
#include <stack>
#include <list>

#include <boost/spirit/include/support_utree.hpp>
#include "boost/lexical_cast.hpp"

namespace metaSMT {
namespace evaluator {
using namespace boost::spirit;

template<typename Context>
struct UTreeEvaluator
{
  enum smt2Symbol
  {
    undefined, setlogic, setoption, getoption, checksat, assertion, declarefun, getvalue, push, pop, exit
  };

  enum smt2operator
  {
    other, smttrue, smtfalse, smtnot, smteq, smtand, smtor, smtxor, smtimplies, smtite, smtbvnot, smtbvand, smtbvor, smtbvxor, smtbvcomp, smtbvadd, smtbvmul, smtbvsub, smtbvdiv, smtbvrem, smtbvsle, smtbvsge, smtbvslt, smtbvsgt
  };

  template<typename T1>
  struct result
  {
    typedef utree::list_type type;
  };

  typedef std::map<std::string, smt2Symbol> SymbolMap;
  typedef std::map<std::string, smt2operator> OperatorMap;
  typedef std::map<std::string, metaSMT::logic::predicate> PredicateMap;
  typedef std::map<std::string, metaSMT::logic::QF_BV::bitvector> BitVectorMap;
  typedef typename Context::result_type result_type;

  UTreeEvaluator(Context& ctx) :
      ctx(ctx)
  {
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
    operatorMap["bvand"] = smtbvand;
    operatorMap["bvor"] = smtbvor;
    operatorMap["bvxor"] = smtbvxor;
    operatorMap["bvcomp"] = smtbvcomp;
    operatorMap["bvadd"] = smtbvadd;
    operatorMap["bvmul"] = smtbvmul;
    operatorMap["bvsub"] = smtbvsub;
    operatorMap["bvdiv"] = smtbvdiv;
    operatorMap["bvrem"] = smtbvrem;
    operatorMap["bvsle"] = smtbvsle;
    operatorMap["bvsge"] = smtbvsge;
    operatorMap["bvslt"] = smtbvslt;
    operatorMap["bvsgt"] = smtbvsgt;
  }

  void printSMT(utree ast)
  {
    parseSymbol(ast);
  }

  void parseSymbol(utree ast)
  {
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
      case checksat:
        if(metaSMT::solve(ctx)){
          std::cout << "sat" << std::endl;
        } else {
          std::cout << "unsat" << std::endl;
        }
        break;
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
        std::cout << metaSMT::read_value(ctx, getVariable(value)) << std::endl;
        break;
      }
      case setoption:
      case getoption:
      case setlogic:
      case exit:
      case undefined:
      default:
        break;
      }
    }
  }

  result_type translateLogicalInstruction(utree tree)
  {
    result_type output;
    switch (tree.which()) {
    case utree_type::list_type: {
      for (utree::iterator I = tree.begin(); I != tree.end(); ++I) {
        std::string value = utreeToString(*I);
        if (operatorMap[value] != other) {
          pushOperator(value);
        } else {
          // handle bitvector
          if (value.compare("_") == 0) {
            ++I;
            std::string bvvalue = utreeToString(*I);
            ++I;
            std::string bitSize = utreeToString(*I);
            pushResultType(createBvInt(bvvalue, bitSize));
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
    case utree_type::string_type: {
      std::string value = utreeToString(tree);
      if (operatorMap[value] != other) {
        pushOperator(value);
      } else {
        pushVarOrConstant(value);
      }
      consume();
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
      default:
        break;
      }
    }
      break;
      // binary operators
    case 2: {
      result_type op1 = popResultType();
      result_type op2 = popResultType();
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
      case smtbvor:
        result = metaSMT::evaluate(ctx, metaSMT::logic::QF_BV::bvor(op1, op2));
        break;
      case smtbvxor:
        result = metaSMT::evaluate(ctx, metaSMT::logic::QF_BV::bvxor(op1, op2));
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
      case smtbvdiv:
        result = metaSMT::evaluate(ctx, metaSMT::logic::QF_BV::bvsdiv(op1, op2));
        break;
      case smtbvrem:
        result = metaSMT::evaluate(ctx, metaSMT::logic::QF_BV::bvsrem(op1, op2));
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
      default:
        break;
      }
    }
      break;
      // ternary operators
    case 3: {
      result_type op1 = popResultType();
      result_type op2 = popResultType();
      result_type op3 = popResultType();
      switch (operatorMap[op]) {
      case smtite:
        result = metaSMT::evaluate(ctx, metaSMT::logic::Ite(op1, op2, op3));
        break;
      default:
        break;
      }
    }
      break;
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

  /* pushes constant Bit/Hex value if value begins with #b/#x
   * otherwise pushes variable if value is an identifier
   * otherwise pushes empty result_type, should crash then
   */
  void pushVarOrConstant(std::string value)
  {
    result_type var = getVariable(value);
    if (value.find("#", 0, 1) != value.npos) {
      if (value.find("b", 1, 1) != value.npos) {
        value.erase(0, 2);
        var = metaSMT::evaluate(ctx, metaSMT::logic::QF_BV::bvbin(value));
      } else if (value.find("x", 1, 1) != value.npos) {
        value.erase(0, 2);
        var = metaSMT::evaluate(ctx, metaSMT::logic::QF_BV::bvhex(value));
      }
    }
    pushResultType(var);
  }

  result_type createBvInt(std::string value, std::string bitSize)
  {
    unsigned number = 0;
    if (value.size() > 2) {
      if (value.find("bv", 0, 2) != value.npos) {
        value.erase(0, 2);
        number = boost::lexical_cast<unsigned>(value);
      }
    }
    unsigned width = boost::lexical_cast<unsigned>(bitSize);
    if(width == 1){
      if(number == 1){
        return metaSMT::evaluate(ctx, metaSMT::logic::QF_BV::bit1);
      } else if(number == 0){
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
    case utree_type::list_type: {
      utree::iterator bitVecIterator = functionType.begin();
      ++bitVecIterator;
      ++bitVecIterator;
      std::string bitSize = utreeToString(*bitVecIterator);
      unsigned width = boost::lexical_cast<unsigned>(bitSize);
      bitVectorMap[functionName] = metaSMT::logic::QF_BV::new_bitvector(width);
      break;
    }
    case utree_type::string_type: {
      predicateMap[functionName] = metaSMT::logic::new_variable();
      break;
    }
    default:
      break;
    }
  }

  result_type getVariable(std::string name)
  {
    // name is a variable identifier, therfore unique and may only be in one map
    PredicateMap::iterator IP = predicateMap.find(name);
    BitVectorMap::iterator IBV = bitVectorMap.find(name);
    result_type output;
    if (IP != predicateMap.end()) {
    	output = metaSMT::evaluate(ctx,predicateMap[name]);
    }
    if (IBV != bitVectorMap.end()) {
      output = metaSMT::evaluate(ctx,bitVectorMap[name]);
    }
    return output;
  }

  int numOperands(std::string op)
  {
    switch (operatorMap[op]) {
    case smttrue:
    case smtfalse:
      return 0;
    case smtnot:
    case smtbvnot:
      return 1;
    case smteq:
    case smtand:
    case smtor:
    case smtxor:
    case smtimplies:
    case smtbvand:
    case smtbvor:
    case smtbvxor:
    case smtbvcomp:
    case smtbvadd:
    case smtbvmul:
    case smtbvsub:
    case smtbvdiv:
    case smtbvrem:
    case smtbvsle:
    case smtbvsge:
    case smtbvslt:
    case smtbvsgt:
      return 2;
    case smtite:
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
  CommandMap commandMap;
  SymbolMap symbolMap;
  OperatorMap operatorMap;

  std::stack<std::string> operatorStack;
  std::stack<std::pair<int, int> > neededOperandStack;

  PredicateMap predicateMap;
  BitVectorMap bitVectorMap;
  std::stack<result_type> resultTypeStack;
  std::list<bool> results;

};
// struct UTreeEvaluator
}// namespace evaluator
}// namespace metaSMT
