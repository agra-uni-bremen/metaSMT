#pragma once 

#include <iostream>
#include <map>
#include <stack>

#include <boost/spirit/include/support_utree.hpp>

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

  enum smt2operator
  {
    other, smteq, smtxor, smtnot, smtimplies, smtor, smtand, smtite, smtbvmul, smtbvand, smtbvnot
  };

  template<typename T1>
  struct result
  {
    typedef boost::spirit::utree::list_type type;
  };

  typedef std::map<std::string, boost::function<bool(boost::spirit::utree::list_type&)> > CommandMap;
  typedef std::map<std::string, smt2Symbol> SymbolMap;
  typedef std::map<std::string, smt2operator> OperatorMap;

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

    operatorMap["not"] = smtnot;
    operatorMap["="] = smteq;
    operatorMap["and"] = smtand;
    operatorMap["or"] = smtor;
    operatorMap["xor"] = smtxor;
    operatorMap["=>"] = smtimplies;
    operatorMap["ite"] = smtite;
    operatorMap["bvmul"] = smtbvmul;
    operatorMap["bvand"] = smtbvand;
    operatorMap["bvnot"] = smtbvnot;
  }

  void print(boost::spirit::utree ast)
  {
    initialize();
    parseSymbol(ast);
//    std::cout << "Ergebnis= " << std::endl;
    std::cout << metaSMTString << std::endl;
  }

  void parseSymbol(boost::spirit::utree ast)
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
          metaSMTString += nestString("assumption ( ctx, ", translateLogicalInstruction(logicalInstruction), ");\n");
        } else {
          metaSMTString += nestString("assertion ( ctx, ", translateLogicalInstruction(logicalInstruction), ");\n");
        }
        break;
      }
      case push: {
        pushed = true;
        break;
      }
      case declarefun: {
        metaSMTString += translateDeclareFunction(command);
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

  std::string translateDeclareFunction(boost::spirit::utree function)
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

  std::string translateLogicalInstruction(boost::spirit::utree tree)
  {
    std::string output = "";
    switch (tree.which()) {
    case boost::spirit::utree::type::list_type: {
      for (boost::spirit::utree::iterator I = tree.begin() ; I != tree.end() ; ++I){
        std::string value = utreeToString(*I);
        if(isOperator(value)){
          operatorStack.push(value);
        } else {
          // handle s.th. like ((_ bv123 32) a)
          if(value.compare("_") == 0){
            ++I;
            std::string nextToken = utreeToString(*I);
            nextToken.erase(0,2);
            ++I;
            std::string bitSize = utreeToString(*I);
            std::string operand = "bvsint(" + nextToken + "," + bitSize + ")";
            operandStack.push(operand);
          } else {
            operandStack.push(value);
          }
        }
        consume();
      }
      output += operandStack.top();
      operandStack.pop();
      break;
    }
    case boost::spirit::utree::type::string_type: {
      std::string value = utreeToString(tree);
      output += value;
      break;
    }
    default:
      break;
    }
    return output;
  }

  void consume()
  {
    if(!operatorStack.empty() && !operandStack.empty()){
      std::string op = operatorStack.top();
      switch (operatorMap[op]) {
      // unary operators
      case smtnot:
      case smtbvnot:
        if(operandStack.size() > 0){
        	std::string op1 = operandStack.top();
        	operandStack.pop();
          std::string newOperand = translateLogicalOerator(op) + op1 + ")";
          operandStack.push(newOperand);
          operatorStack.pop();
        }
        break;
      // binary operators
      case smteq:
      case smtand:
      case smtor:
      case smtxor:
      case smtimplies:
      case smtbvmul:
      case smtbvand:
        if(operandStack.size() >= 2){
          std::string op2 = operandStack.top();
          operandStack.pop();
          std::string op1 = operandStack.top();
          operandStack.pop();
          std::string newOperand = translateLogicalOerator(op) + op1 + "," + op2 + ")";
          operandStack.push(newOperand);
          operatorStack.pop();
        }
        break;
      // ternary operators
      case smtite:
        if(operandStack.size() >= 3){
          std::string op3 = operandStack.top();
          operandStack.pop();
          std::string op2 = operandStack.top();
          operandStack.pop();
          std::string op1 = operandStack.top();
          operandStack.pop();
          std::string newOperand = translateLogicalOerator(op) + op1 + "," + op2 + "," + op3 + ")";
          operandStack.push(newOperand);
          operatorStack.pop();
        }
        break;
      case other:
      default:
        std::cout << "couldn't recognize operator:" << op << std::endl;
        break;
      }
    }
  }

  bool isOperator(std::string op){
    switch (operatorMap[op]) {
    case smteq:
    case smtnot:
    case smtand:
    case smtor:
    case smtxor:
    case smtimplies:
    case smtite:
    case smtbvmul:
    case smtbvand:
    case smtbvnot:
      return true;
    case other:
    default:
      break;
    }
    return false;
  }

  std::string utreeToString(boost::spirit::utree tree)
  {
    std::stringstream stringStream;
    stringStream << tree;
    std::string output = stringStream.str();
    size_t found = output.find("\"");
    while (found != output.npos){
      output.erase(found, 1);
      found = output.find("\"");
    }
    found = output.find(" ");
    while (found != output.npos){
      output.erase(found, 1);
      found = output.find(" ");
    }
    if(output.size() > 2){
      if(output.find("#",0,1) != output.npos){
        if(output.find("b",1,1) != output.npos){
          output.erase(0,2);
          output = "bvbin(\"" + output + "\")";
        } else if (output.find("x",1,1) != output.npos){
          output.erase(0,2);
          output = "bvhex(\"" + output + "\")";
        }
      }
    }
    return output;
  }

  std::string translateLogicalOerator(std::string op)
  {
    switch (operatorMap[op]) {
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
    case smtbvmul:
      return "bvmul(";
    case smtbvand:
      return "bvand(";
    case smtbvnot:
      return "bvnot(";
    default:
      return "undefinedOperator(";
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

};
}
}
