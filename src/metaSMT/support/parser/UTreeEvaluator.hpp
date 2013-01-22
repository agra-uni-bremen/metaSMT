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
#include <boost/mpl/not.hpp>

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

    inline boost::optional< logic::index >
    get_index( std::string const &name ) {
      bool found = false;
      logic::index idx = 0;
      detail::IndexVisitor visitor(found, idx, name);
      mpl::for_each< SMT_NameMap >( visitor );
      if ( found ) {
        return boost::optional< logic::index >(idx);
      }
      else {
        return boost::optional< logic::index >();
      }
    }

    namespace detail {
      template < typename Attr >
      struct HasAttributeVisitor {
        HasAttributeVisitor(bool &found,
                            bool &has_attribute,
                            std::string const &name)
          : found(found)
          , has_attribute(has_attribute)
          , name(name)
        {}

        template < typename Pair >
        void operator()( Pair const & ) {
          typedef typename Pair::first Tag;
          typedef typename Pair::second Name;
          if ( !found &&
               mpl::c_str<Name>::value == name ) {          
            found = true;
            has_attribute = boost::is_same<typename Tag::attribute, Attr>::value;
          }
        }

        bool &found;
        bool &has_attribute;
        std::string const name;
      }; // IndexVisitor
    } // detail

    template < typename Attr >
    bool has_attribute( std::string const &name ) {
      bool found = false;
      bool has_attribute = false;
      detail::HasAttributeVisitor<Attr> visitor(found, has_attribute, name);
      mpl::for_each< SMT_NameMap >( visitor );
      assert( found );
      return has_attribute;
    }

    template < typename Context, typename Tag, typename T, typename Arg >
    typename boost::disable_if<
      typename boost::mpl::not_<
        typename boost::is_same<typename Tag::attribute, attr::ignore>::type
      >::type
    , typename Context::result_type
    >::type
    callCtx( Context *ctx, Tag const &, Arg arg, std::vector<T> const &args ) {
      assert( false && "Unsupported attribute" );
      return evaluate(*ctx, logic::False);
    }

    template < typename Context, typename Tag, typename T, typename Arg >
    typename boost::disable_if<
      typename boost::mpl::not_<
        typename boost::is_same<typename Tag::attribute, attr::constant>::type
      >::type
    , typename Context::result_type
    >::type
    callCtx( Context *ctx, Tag const &, Arg arg, std::vector<T> const &args ) {
      return (*ctx)(Tag());
    }

    template < typename Context, typename Tag, typename T, typename Arg >
    typename boost::disable_if<
      typename boost::mpl::not_<
        typename boost::is_same<typename Tag::attribute, attr::unary>::type
      >::type
    , typename Context::result_type
    >::type
    callCtx( Context *ctx, Tag const &, Arg arg, std::vector<T> const &args ) {
      return (*ctx)(Tag(), boost::proto::lit(args[0]));
    }

    template < typename Context, typename T >
    typename Context::result_type
    callCtx( Context *ctx,
             bvtags::extract_tag const &,
             boost::tuple<unsigned long, unsigned long> const &tuple,
             std::vector<T> const &args ) {
      unsigned long const op0 = tuple.get<0>();
      unsigned long const op1 = tuple.get<1>();
      return (*ctx)(bvtags::extract_tag(), boost::proto::lit(op0), boost::proto::lit(op1), boost::proto::lit(args[0]));
    }

    template < typename Context, typename T >
    typename Context::result_type
    callCtx( Context *ctx,
             bvtags::zero_extend_tag const &,
             boost::tuple<unsigned long> const &tuple,
             std::vector<T> const &args ) {
      unsigned long const w = tuple.get<0>();
      return (*ctx)(bvtags::zero_extend_tag(), boost::proto::lit(w), boost::proto::lit(args[0]));
    }

    template < typename Context, typename T >
    typename Context::result_type
    callCtx( Context *ctx,
             bvtags::sign_extend_tag const &,
             boost::tuple<unsigned long> const &tuple,
             std::vector<T> const &args ) {
      unsigned long const w = tuple.get<0>();
      return (*ctx)(bvtags::sign_extend_tag(), boost::proto::lit(w), boost::proto::lit(args[0]));
    }

    template < typename Context, typename Tag, typename T, typename Arg >
    typename boost::disable_if<
      typename boost::mpl::not_<
        typename boost::is_same<typename Tag::attribute, attr::binary>::type
      >::type
    , typename Context::result_type
    >::type
    callCtx( Context *ctx, Tag const &, Arg tuple, std::vector<T> const &args ) {
      return (*ctx)(Tag(), boost::proto::lit(args[0]), boost::proto::lit(args[1]));
    }

    template < typename Context, typename Tag, typename T, typename Arg >
    typename boost::disable_if<
      typename boost::mpl::not_<
        typename boost::is_same<
          typename Tag::attribute
        , attr::ternary
        >::type
      >::type
    , typename Context::result_type
    >::type
    callCtx( Context *ctx, Tag const &, Arg tuple, std::vector<T> const &args ) {
      return (*ctx)(Tag(), boost::proto::lit(args[0]), boost::proto::lit(args[1]), boost::proto::lit(args[2]));
    }

    template < typename Context, typename T, typename Arg >
    struct CallByIndexVisitor {
      CallByIndexVisitor(Context *ctx,
              bool &found,
              typename Context::result_type &r,
              logic::index idx,
              std::vector<T> const &args,
              Arg arg)
        : ctx(ctx)
        , found(found)
        , r(r)
        , idx(idx)
        , args(args)
        , arg(arg)
      {}

      template < typename Tag >
      void operator()( Tag const & ) {
        if ( !found &&
             logic::Index<Tag>::value == idx ) {
          found = true;
          r = callCtx(ctx, Tag(), arg, args);
        }
      }

      Context *ctx;
      bool &found;
      typename Context::result_type &r;
      logic::index idx;
      std::vector<T> const &args;
      Arg arg;
    }; // CallByIndexVisitor

    template < typename Context >
    struct CallByIndex {
      CallByIndex(Context &ctx)
        : ctx(ctx)
      {}

      template < typename T, typename Arg >
      typename Context::result_type
      callByIndex( logic::index idx,
                   std::vector<T> const &args,
                   Arg p) {
        bool found = false;
        typename Context::result_type r;
        CallByIndexVisitor<Context, T, Arg> visitor(&ctx, found, r, idx, args, p);
        boost::mpl::for_each< _all_logic_tags::all_Tags >(visitor);
        assert( found );
        return r;
      }
      
      template < typename Arg >
      typename Context::result_type operator()( logic::index idx,
                                                Arg arg) {
        std::vector< typename Context::result_type > args;
        return callByIndex(idx, args, arg);
      }

      template < typename T, typename Arg >
      typename Context::result_type operator()( logic::index idx,
                                                Arg arg,
                                                T const &op0 ) {
        std::vector< typename Context::result_type > args;
        args.push_back( op0 );
        return callByIndex(idx, args, arg);
      }

      template < typename T, typename Arg >
      typename Context::result_type operator()( logic::index idx,
                                                Arg arg,
                                                T const &op0,
                                                T const &op1 ) {
        std::vector< typename Context::result_type > args;
        args.push_back( op0 );
        args.push_back( op1 );
        return callByIndex(idx, args, arg);
      }

      template < typename T, typename Arg >
      typename Context::result_type operator()( logic::index idx,
                                                Arg arg,
                                                T const &op0,
                                                T const &op1,
                                                T const &op2 ) {
        std::vector< typename Context::result_type > args;
        args.push_back( op0 );
        args.push_back( op1 );
        args.push_back( op2 );
        return callByIndex(idx, args, arg);
      }

      Context &ctx;
    }; // CallByIndex

template<typename Context>
struct UTreeEvaluator
{
  enum SMT_symbol {
    undefined
  , setlogic
  , setoption
  , getoption
  , checksat
  , assertion
  , declarefun
  , getvalue
  , push
  , pop
  , exit
  };

  typedef typename Context::result_type result_type;
  typedef boost::spirit::utree utree;
  typedef std::map<std::string, SMT_symbol> SymbolMap;
  typedef type::TypedSymbol<Context> TypedSymbol;
  typedef boost::shared_ptr< TypedSymbol > TypedSymbolPtr;
  typedef std::map<std::string, TypedSymbolPtr > VarMap;

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
        r = evaluate(ctx, logic::And(r, translateLogicalInstruction(*utree_it)));
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
      std::string const symbolString = utreeToString(symbol);

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
        boost::optional< logic::index > idx = get_index(value);
        if ( idx ) {
          pushOperator(value);
        }
        else {
          // handle bitvector
          if (value.compare("_") == 0) {
            ++I;
            std::string bvvalue = utreeToString(*I);
            boost::optional< logic::index > idx = get_index(bvvalue);
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
      boost::optional< logic::index > idx = get_index(value);
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
    std::string const op = operatorStack.top();
    result_type result;
    switch ( getOpArity(op) ) {
    // constants
    case 0: {
      boost::optional< logic::index > idx = get_index(op);
      assert( idx );
      result = CallByIndex<Context>(ctx)(*idx, boost::make_tuple());
      break;
    }
    // unary operators
    case 1: {
      boost::optional< logic::index > idx = get_index(op);
      assert( idx );
      if ( *idx == logic::Index<bvtags::extract_tag>::value ) {
        result_type op0 = popResultType();
        unsigned long const lower = popModBvLengthParam();
        unsigned long const upper = popModBvLengthParam();
        result = CallByIndex<Context>(ctx)(*idx, boost::make_tuple(upper, lower), op0);
      }
      else if ( *idx == logic::Index<bvtags::zero_extend_tag>::value ||
                *idx == logic::Index<bvtags::sign_extend_tag>::value ) {
        unsigned long const width = popModBvLengthParam();
        result_type op0 = popResultType();
        result = CallByIndex<Context>(ctx)(*idx, boost::make_tuple(width), op0);
      }
      else {
        result_type op0 = popResultType();
        result = CallByIndex<Context>(ctx)(*idx, boost::make_tuple(), op0);
      }
      break;
    }
    // binary operators
    case 2: {
      boost::optional< logic::index > idx = get_index(op);
      assert( idx );
      result_type op1 = popResultType();
      result_type op0 = popResultType();
      result = CallByIndex<Context>(ctx)(*idx, boost::make_tuple(), op0, op1);
      break;
    }
    // ternary operators
    case 3: {
      boost::optional< logic::index > idx = get_index(op);
      assert( idx );
      if ( *idx == logic::Index<predtags::ite_tag>::value ) {
        result_type op2 = popResultType();
        result_type op1 = popResultType();
        result_type op0 = popResultType();
        result = CallByIndex<Context>(ctx)(*idx, boost::make_tuple(), op0, op1, op2);
      }
      else {
        assert( false );
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

  void pushOperator(std::string const &op) {
    operatorStack.push(op);

    int num_operands;
    boost::optional< logic::index > idx = get_index(op);
    assert( idx );
    if ( *idx == logic::Index<bvtags::zero_extend_tag>::value ||
         *idx == logic::Index<bvtags::sign_extend_tag>::value ) {
      num_operands = 2;
    }
    else if ( *idx == logic::Index<bvtags::extract_tag>::value ) {
      num_operands = 3;
    }
    else {
      num_operands = getOpArity(op);
    }

    std::pair<int, int> neededOperands(num_operands, 0);
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

  void pushModBvLengthParam(int op) {
    if (neededOperandStack.size() > 0) {
      std::pair<int, int> newTop(neededOperandStack.top().first, neededOperandStack.top().second + 1);
      neededOperandStack.pop();
      neededOperandStack.push(newTop);
    }
    modBvLengthParamStack.push(op);
  }

  result_type popResultType() {
    result_type op = resultTypeStack.top();
    resultTypeStack.pop();
    return op;
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

  unsigned char getOpArity(std::string const &op) const {
    if ( has_attribute<attr::constant>(op) ) {
      return 0;
    }
    else if ( has_attribute<attr::unary>(op) ) {
      return 1;
    }
    else if ( has_attribute<attr::binary>(op) ) {
      return 2;
    }
    else if ( has_attribute<attr::ternary>(op) ) {
      return 3;
    }
    assert( false );
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
