#pragma once 

#include "../../tags/QF_BV.hpp"
#include "../../tags/Array.hpp"
#include "../../result_wrapper.hpp"

#include <iostream>
#include <map>
#include <stack>

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
    undefined, setlogic, setoption, checksat, assertion, declarefun, getvalue, push, pop, exit
  };

  // TODO: check which bv constant/length/shift/comparison operators exist in SMT2
  enum smt2operator
  {
    other, smttrue, smtfalse, smtnot, smteq, smtand, smtor, smtxor, smtimplies, smtite, smtbvnot, smtbvand, smtbvor, smtbvxor, smtbvcomp, smtbvadd, smtbvmul, smtbvsub, smtbvdiv, smtbvrem
  };

  template<typename T1>
  struct result
  {
    typedef boost::spirit::utree::list_type type;
  };

  typedef std::map<std::string, boost::function<bool(boost::spirit::utree::list_type&)> > CommandMap;
  typedef std::map<std::string, smt2Symbol> SymbolMap;
  typedef std::map<std::string, smt2operator> OperatorMap;
  typedef typename Context::result_type result_type;

  UTreeEvaluator(Context& ctx) :
      ctx(ctx)
  {
  }

  boost::spirit::utree::list_type& operator()(boost::spirit::utree::list_type& ast) const
  {

    assert( ast.which() == utree::list_type());
    std::cout << ast << std::endl;
//        std::string command_name = ast.begin();
    ast.clear();
    return ast;
  }

  void initialize()
  {
    symbolMap["set-logic"] = setlogic;
    symbolMap["set-option"] = setoption;
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
  }

  void print(boost::spirit::utree ast)
  {
    initialize();
    parseSymbolToString(ast);
    std::cout << metaSMTString << std::endl;
  }

  void solve(boost::spirit::utree ast)
  {
    initialize();
    parseSymbolToResultType(ast);
  }

  void parseSymbolToResultType(boost::spirit::utree ast)
  {
    bool pushed = false;
    for (boost::spirit::utree::iterator I = ast.begin(); I != ast.end(); ++I) {
      boost::spirit::utree command = *I;
      boost::spirit::utree::iterator commandIterator = command.begin();
      boost::spirit::utree symbol = *commandIterator;
      std::string symbolString = utreeToString(symbol);

      switch (symbolMap[symbolString]) {
      case push:
        pushed = true;
        break;
      case checksat:
        pushed = false;
        std::cout << metaSMT::solve(ctx) << std::endl;
        break;
      case assertion: {
        ++commandIterator;
        boost::spirit::utree logicalInstruction = *commandIterator;
//        std::cout << "logicalInstruction: " << logicalInstruction << std::endl;
        if (pushed) {
          metaSMT::assumption(ctx,translateLogicalInstructionToResultType(logicalInstruction));
        } else {
          metaSMT::assertion(ctx,translateLogicalInstructionToResultType(logicalInstruction));
        }
//        std::cout << "End: " << "operand= " << resultTypeStack.size() << " operator= " << operatorStack.size() << " neededStack= " << neededOperandStack.size() << std::endl;
        break;
      }
      case declarefun:
      case getvalue:
      case setoption:
      case setlogic:
      case pop:
      case exit:
      case undefined:
      default:
        break;
      }
    }
  }

  result_type translateLogicalInstructionToResultType(boost::spirit::utree tree)
  {
    result_type output;
    switch (tree.which()) {
    case boost::spirit::utree::type::list_type: {
      for (boost::spirit::utree::iterator I = tree.begin(); I != tree.end(); ++I) {
        std::string value = utreeToString(*I);
//        std::cout << "value= " << value << std::endl;
        if (operatorMap[value] != other) {
          operatorStack.push(value);
          std::pair<int, int> newOperandStackValue(numOperands(value), 0);
          neededOperandStack.push(newOperandStackValue);
        } else {
//          // create var_tags
          if (value.compare("_") == 0) {
            ++I;
            ++I;
            std::string bitSize = utreeToString(*I);
            metaSMT::logic::QF_BV::tag::var_tag tag;
            unsigned width = boost::lexical_cast<unsigned>(bitSize);
            tag.width = width;
            pushResultType(ctx(tag));
          } else {
            metaSMT::logic::tag::var_tag tag;
            pushResultType(ctx(tag));
          }
        }
        while (canConsume()) {
//          std::cout << "before: " << "operand= " << resultTypeStack.size() << " operator= " << operatorStack.size() << " neededStack= " << neededOperandStack.size() << std::endl;
          consumeToResultType();
//          std::cout << "after: " << "operand= " << resultTypeStack.size() << " operator= " << operatorStack.size() << " neededStack= " << neededOperandStack.size() << std::endl;
        }
      }
      break;
    }
    case boost::spirit::utree::type::string_type: {
      std::string value = utreeToString(tree);
      if (operatorMap[value] != other) {
        operatorStack.push(value);
        std::pair<int, int> newOperandStackValue(numOperands(value), 0);
        neededOperandStack.push(newOperandStackValue);
      } else {
        metaSMT::logic::tag::var_tag tag;
        resultTypeStack.push(ctx(tag));
      }
      consumeToResultType();
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

  void consumeToResultType()
  {
    std::string op = operatorStack.top();
    result_type result;
    switch(numOperands(op)){
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
        result = metaSMT::evaluate(ctx, metaSMT::logic::equal(op1,op2));
        break;
      default:
        break;
      }
    }
      break;
    // ternary operators
    case 3:
      break;
    default:
      break;
    }

    neededOperandStack.pop();
    pushResultType(result);
    operatorStack.pop();
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

  void parseSymbolToString(boost::spirit::utree ast)
  {
    bool pushed = false;
    for (boost::spirit::utree::iterator I = ast.begin(); I != ast.end(); ++I) {
      boost::spirit::utree command = *I;
      boost::spirit::utree::iterator commandIterator = command.begin();
      boost::spirit::utree symbol = *commandIterator;
      std::string symbolString = utreeToString(symbol);

      switch (symbolMap[symbolString]) {
      case checksat:
        pushed = false;
        metaSMTString += "BOOST_REQUIRE( solve(ctx) );\n";
        break;
      case assertion: {
        ++commandIterator;
        boost::spirit::utree logicalInstruction = *commandIterator;
//        std::cout << "logicalInstruction: " << logicalInstruction << std::endl;
        if (pushed) {
          metaSMTString += nestString("assumption ( ctx, ", translateLogicalInstructionToString(logicalInstruction), ");\n");
        } else {
          metaSMTString += nestString("assertion ( ctx, ", translateLogicalInstructionToString(logicalInstruction), ");\n");
        }
        break;
      }
      case push: {
        pushed = true;
        break;
      }
      case declarefun: {
        metaSMTString += translateDeclareFunctionToString(command);
        break;
      }
      case getvalue: {
        ++commandIterator;
        boost::spirit::utree valueName = *commandIterator;
        metaSMTString += nestString("read_value(ctx,", utreeToString(valueName), ");\n");
        break;
      }
      case setoption:
      case setlogic:
      case pop:
      case exit:
      case undefined:
      default:
        break;
      }
    }
  }

  std::string translateLogicalInstructionToString(boost::spirit::utree tree)
  {
    std::string output = "";
    switch (tree.which()) {
    case boost::spirit::utree::type::list_type: {
      for (boost::spirit::utree::iterator I = tree.begin(); I != tree.end(); ++I) {
        std::string value = utreeToString(*I);
//        std::cout << "value= " << value << std::endl;
        if (operatorMap[value] != other) {
          operatorStack.push(value);
          std::pair<int, int> newOperandStackValue(numOperands(value), 0);
          neededOperandStack.push(newOperandStackValue);
        } else {
          // handle s.th. like ((_ bv123 32) a)
          if (value.compare("_") == 0) {
            ++I;
            std::string nextToken = utreeToString(*I);
            nextToken.erase(0, 2);
            ++I;
            std::string bitSize = utreeToString(*I);
            std::string operand = "bvsint(" + nextToken + "," + bitSize + ")";
            pushOperandToString(operand);
          } else {
            pushOperandToString(value);
          }
        }
        while (canConsume()) {
//          std::cout << "before: " << "operand= " << operandStack.size() << " operator= " << operatorStack.size() << " neededStack= " << neededOperandStack.size() << std::endl;
          consumeToString();
//          std::cout << "after: " << "operand= " << operandStack.size() << " operator= " << operatorStack.size() << " neededStack= " << neededOperandStack.size() << std::endl;
        }
      }
      break;
    }
    case boost::spirit::utree::type::string_type: {
      std::string value = utreeToString(tree);
      operandStack.push(value);
      break;
    }
    default:
      break;
    }
    output += operandStack.top();
    operandStack.pop();
    return output;
  }

  void consumeToString()
  {
    std::string op = operatorStack.top();
    switch (operatorMap[op]) {
    // constants
    case smttrue:
    case smtfalse: {
      std::string newOperand = translateLogicalOeratorToString(op);
      neededOperandStack.pop();
      pushOperandToString(newOperand);
      operatorStack.pop();
    }
      break;
      // unary operators
    case smtnot:
    case smtbvnot: {
      std::string op1 = operandStack.top();
      operandStack.pop();
      std::string newOperand = translateLogicalOeratorToString(op) + op1 + ")";
      neededOperandStack.pop();
      pushOperandToString(newOperand);
      operatorStack.pop();
    }
      break;
      // binary operators
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
    case smtbvrem: {
      std::string op2 = operandStack.top();
      operandStack.pop();
      std::string op1 = operandStack.top();
      operandStack.pop();
      std::string newOperand = translateLogicalOeratorToString(op) + op1 + "," + op2 + ")";
      neededOperandStack.pop();
      pushOperandToString(newOperand);
      operatorStack.pop();
    }
      break;
      // ternary operators
    case smtite: {
      std::string op3 = operandStack.top();
      operandStack.pop();
      std::string op2 = operandStack.top();
      operandStack.pop();
      std::string op1 = operandStack.top();
      operandStack.pop();
      std::string newOperand = translateLogicalOeratorToString(op) + op1 + "," + op2 + "," + op3 + ")";
      neededOperandStack.pop();
      pushOperandToString(newOperand);
      operatorStack.pop();
    }
      break;
    case other:
    default:
      std::cout << "couldn't recognize operator:" << op << std::endl;
      break;
    }
  }

  std::string translateDeclareFunctionToString(boost::spirit::utree function)
  {
    // (declare-fun var_1 () (_ BitVec 8))
    // bitvector x = new_bitvector(8);
    // (declare-fun var_1 () Bool)
    // predicate x = new_variable();
    boost::spirit::utree::iterator functionIterator = function.begin();
    ++functionIterator;
    std::string functionName = utreeToString(*functionIterator);
    ++functionIterator;
    ++functionIterator;
    boost::spirit::utree functionType = *functionIterator;
    std::string output = "";

    switch (functionType.which()) {
    case boost::spirit::utree::type::list_type: {
      boost::spirit::utree::iterator bitVecIterator = functionType.begin();
      ++bitVecIterator;
      ++bitVecIterator;
      std::string bitSize = utreeToString(*bitVecIterator);
      output = "bitvector " + functionName + " = new_bitvector(" + bitSize + ");\n";
      break;
    }
    case boost::spirit::utree::type::string_type: {
      output = "predicate " + functionName + " = new_variable();\n";
      break;
    }
    default:
      break;
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

  void pushOperandToString(std::string op)
  {
    if (neededOperandStack.size() > 0) {
      std::pair<int, int> newTop(neededOperandStack.top().first, neededOperandStack.top().second + 1);
      neededOperandStack.pop();
      neededOperandStack.push(newTop);
    }
    operandStack.push(op);
  }

  std::string utreeToString(boost::spirit::utree tree)
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
    if (output.size() > 2) {
      if (output.find("#", 0, 1) != output.npos) {
        if (output.find("b", 1, 1) != output.npos) {
          output.erase(0, 2);
          output = "bvbin(\"" + output + "\")";
        } else if (output.find("x", 1, 1) != output.npos) {
          output.erase(0, 2);
          output = "bvhex(\"" + output + "\")";
        }
      }
    }
    return output;
  }

  std::string translateLogicalOeratorToString(std::string op)
  {
    switch (operatorMap[op]) {
    case smttrue:
      return "true";
    case smtfalse:
      return "false";
    case smteq:
      return "metaSMT::logic::equal(";
    case smtnot:
      return "Not(";
    case smtand:
      return "And(";
    case smtor:
      return "Or(";
    case smtxor:
      return "Xor(";
    case smtimplies:
      return "implies(";
    case smtite:
      return "Ite(";
    case smtbvnot:
      return "bvnot(";
    case smtbvand:
      return "bvand(";
    case smtbvor:
      return "bvor(";
    case smtbvxor:
      return "bvxor(";
    case smtbvcomp:
      return "bvcomp(";
    case smtbvadd:
      return "bvadd(";
    case smtbvmul:
      return "bvmul(";
    case smtbvsub:
      return "bvsub(";
    case smtbvdiv:
      return "bvdiv(";
    case smtbvrem:
      return "bvrem(";
    default:
      return "undefinedOperator";
    }
    return "";
  }

  std::string nestString(std::string pre, std::string nest, std::string post)
  {
    return pre + nest + post;
  }

private:
  Context& ctx;
  CommandMap commandMap;
  SymbolMap symbolMap;
  OperatorMap operatorMap;

  std::string metaSMTString;
  std::stack<std::string> operatorStack;
  std::stack<std::string> operandStack;
  std::stack<std::pair<int, int> > neededOperandStack;

  std::stack<result_type> resultTypeStack;

};
// struct UTreeEvaluator
}// namespace evaluator
} // namespace metaSMT
