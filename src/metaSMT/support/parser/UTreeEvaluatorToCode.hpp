#pragma once 

#include "UTreeEvaluator.hpp"

namespace metaSMT {
namespace evaluator {
using namespace boost::spirit;

template<typename Context>
struct UTreeEvaluatorToCode: UTreeEvaluator<Context>
{
  typedef UTreeEvaluator<Context> UTreeE;

  UTreeEvaluatorToCode(Context& ctx) :
      UTreeEvaluator<Context>(ctx)
  {
  }

  void print(utree ast)
  {
    parseSymbol(ast);
    std::cout << metaSMTString << std::endl;
  }

  void parseSymbol(utree ast)
  {
    bool pushed = false;
    for (utree::iterator I = ast.begin(); I != ast.end(); ++I) {
      utree command = *I;
      utree::iterator commandIterator = command.begin();
      utree symbol = *commandIterator;
      std::string symbolString = utreeToString(symbol);

      switch (UTreeE::symbolMap[symbolString]) {
      case UTreeE::checksat:
        pushed = false;
        break;
      case UTreeE::assertion: {
        ++commandIterator;
        utree logicalInstruction = *commandIterator;
        if (pushed) {
          metaSMTString += nestString("assumption ( ctx, ", translateLogicalInstruction(logicalInstruction), ");\n");
        } else {
          metaSMTString += nestString("assertion ( ctx, ", translateLogicalInstruction(logicalInstruction), ");\n");
        }
        break;
      }
      case UTreeE::push: {
        pushed = true;
        break;
      }
      case UTreeE::declarefun: {
        metaSMTString += translateDeclareFunction(command);
        break;
      }
      case UTreeE::getvalue: {
        ++commandIterator;
        utree valueName = *commandIterator;
        metaSMTString += nestString("read_value(ctx,", utreeToString(valueName), ");\n");
        break;
      }
      case UTreeE::setoption:
      case UTreeE::setlogic:
      case UTreeE::pop:
      case UTreeE::exit:
      case UTreeE::undefined:
      default:
        break;
      }
    }
  }

  std::string translateLogicalInstruction(utree tree)
  {
    std::string output = "";
    switch (tree.which()) {
    case utree_type::list_type: {
      for (utree::iterator I = tree.begin(); I != tree.end(); ++I) {
        std::string value = utreeToString(*I);
        if (UTreeE::operatorMap[value] != UTreeE::other) {
          UTreeE::operatorStack.push(value);
          std::pair<int, int> newOperandStackValue(UTreeE::numOperands(value), 0);
          UTreeE::neededOperandStack.push(newOperandStackValue);
        } else {
          // handle bitvector
          if (value.compare("_") == 0) {
            ++I;
            std::string nextToken = utreeToString(*I);
            nextToken.erase(0, 2);
            ++I;
            std::string bitSize = utreeToString(*I);
            std::string operand = "bvsint(" + nextToken + "," + bitSize + ")";
            pushOperand(operand);
          } else {
            pushOperand(value);
          }
        }
        while (UTreeE::canConsume()) {
          consume();
        }
      }
      break;
    }
    case utree_type::string_type: {
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

  std::string translateDeclareFunction(utree function)
  {
    utree::iterator functionIterator = function.begin();
    ++functionIterator;
    std::string functionName = utreeToString(*functionIterator);
    ++functionIterator;
    ++functionIterator;
    utree functionType = *functionIterator;
    std::string output = "";

    switch (functionType.which()) {
    case utree_type::list_type: {
      utree::iterator bitVecIterator = functionType.begin();
      ++bitVecIterator;
      ++bitVecIterator;
      std::string bitSize = utreeToString(*bitVecIterator);
      output = "bitvector " + functionName + " = new_bitvector(" + bitSize + ");\n";
      break;
    }
    case utree_type::string_type: {
      output = "predicate " + functionName + " = new_variable();\n";
      break;
    }
    default:
      break;
    }
    return output;
  }

  void consume()
  {
    std::string op = UTreeE::operatorStack.top();
    switch (UTreeE::operatorMap[op]) {
    // constants
    case UTreeE::smttrue:
    case UTreeE::smtfalse: {
      std::string newOperand = translateLogicalOerator(op);
      UTreeE::neededOperandStack.pop();
      pushOperand(newOperand);
      UTreeE::operatorStack.pop();
    }
      break;
      // unary operators
    case UTreeE::smtnot:
    case UTreeE::smtbvnot: {
      std::string op1 = operandStack.top();
      operandStack.pop();
      std::string newOperand = translateLogicalOerator(op) + op1 + ")";
      UTreeE::neededOperandStack.pop();
      pushOperand(newOperand);
      UTreeE::operatorStack.pop();
    }
      break;
      // binary operators
    case UTreeE::smteq:
    case UTreeE::smtand:
    case UTreeE::smtor:
    case UTreeE::smtxor:
    case UTreeE::smtimplies:
    case UTreeE::smtbvand:
    case UTreeE::smtbvor:
    case UTreeE::smtbvxor:
    case UTreeE::smtbvcomp:
    case UTreeE::smtbvadd:
    case UTreeE::smtbvmul:
    case UTreeE::smtbvsub:
    case UTreeE::smtbvdiv:
    case UTreeE::smtbvrem: {
      std::string op2 = operandStack.top();
      operandStack.pop();
      std::string op1 = operandStack.top();
      operandStack.pop();
      std::string newOperand = translateLogicalOerator(op) + op1 + "," + op2 + ")";
      UTreeE::neededOperandStack.pop();
      pushOperand(newOperand);
      UTreeE::operatorStack.pop();
    }
      break;
      // ternary operators
    case UTreeE::smtite: {
      std::string op3 = operandStack.top();
      operandStack.pop();
      std::string op2 = operandStack.top();
      operandStack.pop();
      std::string op1 = operandStack.top();
      operandStack.pop();
      std::string newOperand = translateLogicalOerator(op) + op1 + "," + op2 + "," + op3 + ")";
      UTreeE::neededOperandStack.pop();
      pushOperand(newOperand);
      UTreeE::operatorStack.pop();
    }
      break;
    case UTreeE::other:
    default:
      std::cout << "couldn't recognize operator:" << op << std::endl;
      UTreeE::neededOperandStack.pop();
      UTreeE::operatorStack.pop();
      break;
    }
  }

  std::string translateLogicalOerator(std::string op)
  {
    switch (UTreeE::operatorMap[op]) {
    case UTreeE::smttrue:
      return "true";
    case UTreeE::smtfalse:
      return "false";
    case UTreeE::smteq:
      return "metaSMT::logic::equal(";
    case UTreeE::smtnot:
      return "Not(";
    case UTreeE::smtand:
      return "And(";
    case UTreeE::smtor:
      return "Or(";
    case UTreeE::smtxor:
      return "Xor(";
    case UTreeE::smtimplies:
      return "implies(";
    case UTreeE::smtite:
      return "Ite(";
    case UTreeE::smtbvnot:
      return "bvnot(";
    case UTreeE::smtbvand:
      return "bvand(";
    case UTreeE::smtbvor:
      return "bvor(";
    case UTreeE::smtbvxor:
      return "bvxor(";
    case UTreeE::smtbvcomp:
      return "bvcomp(";
    case UTreeE::smtbvadd:
      return "bvadd(";
    case UTreeE::smtbvmul:
      return "bvmul(";
    case UTreeE::smtbvsub:
      return "bvsub(";
    case UTreeE::smtbvdiv:
      return "bvdiv(";
    case UTreeE::smtbvrem:
      return "bvrem(";
    default:
      return "undefinedOperator";
    }
    return "";
  }

  void pushOperand(std::string op)
  {
    if (UTreeE::neededOperandStack.size() > 0) {
      std::pair<int, int> newTop(UTreeE::neededOperandStack.top().first, UTreeE::neededOperandStack.top().second + 1);
      UTreeE::neededOperandStack.pop();
      UTreeE::neededOperandStack.push(newTop);
    }
    operandStack.push(op);
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

  std::string nestString(std::string pre, std::string nest, std::string post)
  {
    return pre + nest + post;
  }

private:
  std::string metaSMTString;
  std::stack<std::string> operandStack;
};

} // namespace evaluator
} // namespace metaSMT
