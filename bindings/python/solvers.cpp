#include <metaSMT/support/disable_warnings.hpp>
#include <boost/python.hpp>
#include <metaSMT/support/enable_warnings.hpp>

#include "solvers.hpp"

#include <metaSMT/API/SymbolTable.hpp>

using namespace boost::python;

template<typename T>
solver make_solver()
{
  return solver( boost::shared_ptr<T>( new T() ) );
}

template<typename T>
struct evaluate_expression_visitor : public boost::static_visitor<typename T::result_type>
{
  typedef typename T::result_type result_type;

  explicit evaluate_expression_visitor( T& _solver ) : _solver( _solver ) {}

  typename T::result_type operator()( bool expr ) const
  {
    if ( expr )
    {
      return metaSMT::evaluate( _solver, metaSMT::logic::True );
    }
    else
    {
      return metaSMT::evaluate( _solver, metaSMT::logic::False );
    }
  }

  typename T::result_type operator()( const metaSMT::logic::QF_BV::QF_BV<boost::proto::terminal<metaSMT::logic::QF_BV::tag::bit0_tag>::type>& ) const
  {
    return metaSMT::evaluate( _solver, metaSMT::logic::QF_BV::bit0 );
  }

  typename T::result_type operator()( const metaSMT::logic::QF_BV::QF_BV<boost::proto::terminal<metaSMT::logic::QF_BV::tag::bit1_tag>::type>& ) const
  {
    return metaSMT::evaluate( _solver, metaSMT::logic::QF_BV::bit1 );
  }

  typename T::result_type operator()( const metaSMT::logic::predicate& pred ) const
  {
    return metaSMT::evaluate( _solver, pred );
  }

  typename T::result_type operator()( const metaSMT::logic::QF_BV::bitvector& bv ) const
  {
    return metaSMT::evaluate( _solver, bv );
  }

  typename T::result_type operator()( const bvuint_expression& expr ) const
  {
    return metaSMT::evaluate( _solver, metaSMT::logic::QF_BV::bvuint( expr.value, expr.width ) );
  }

  typename T::result_type operator()( const bvsint_expression& expr ) const
  {
    return metaSMT::evaluate( _solver, metaSMT::logic::QF_BV::bvsint( expr.value, expr.width ) );
  }

  template<typename Tag>
  typename T::result_type operator()( const bvstr_expression<Tag>& expr ) const
  {
    return metaSMT::evaluate( _solver, proto::make_expr<Tag>( boost::cref( expr.value ) ) );
  }

  template<typename LogicTag, typename Tag>
  typename T::result_type operator()( const unary_expression<LogicTag, Tag>& expr ) const
  {
    return metaSMT::evaluate( _solver, proto::make_expr<Tag>( boost::cref( boost::apply_visitor( *this, expr.expr ) ) ) );
  }

  template<typename LogicTag, typename Tag>
  typename T::result_type operator()( const binary_expression<LogicTag, Tag>& expr ) const
  {
    return metaSMT::evaluate( _solver, proto::make_expr<Tag>( boost::cref( boost::apply_visitor( *this, expr.left ) ), boost::cref( boost::apply_visitor( *this, expr.right ) ) ) );
  }

  template<typename LogicTag, typename Tag>
  typename T::result_type operator()( const ternary_expression<LogicTag, Tag>& expr ) const
  {
    return metaSMT::evaluate( _solver, proto::make_expr<Tag>( boost::cref( boost::apply_visitor( *this, expr.expr1 ) ), boost::cref( boost::apply_visitor( *this, expr.expr2 ) ), boost::cref( boost::apply_visitor( *this, expr.expr3 ) ) ) );
  }

  template<typename Tag>
  typename T::result_type operator()( const extend_expression<Tag>& expr ) const
  {
    return metaSMT::evaluate( _solver, proto::make_expr<Tag>( boost::cref( expr.by ), boost::cref( boost::apply_visitor( *this, expr.expr ) ) ) );
  }

  template<typename Tag>
  typename T::result_type operator()( const extract_expression<Tag>& expr ) const
  {
    return metaSMT::evaluate( _solver, proto::make_expr<Tag>( boost::cref( expr.from ), boost::cref( expr.width ), boost::cref( boost::apply_visitor( *this, expr.expr ) ) ) );
  }

private:
  T& _solver;
};

struct assertion_visitor : public boost::static_visitor<>
{
  explicit assertion_visitor( const logic_expression& expr ) : expr( expr ) {}

  template<typename T>
  void operator()( const boost::shared_ptr<T>& s ) const
  {
    metaSMT::assertion( *s, boost::apply_visitor( evaluate_expression_visitor<T>( *s ), expr ) );
  }

private:
  const logic_expression& expr;
};

void py_assertion( const solver& ctx, const logic_expression& expr )
{
  boost::apply_visitor( assertion_visitor( expr ), ctx );
}

struct solve_visitor : public boost::static_visitor<bool>
{
  template<typename T>
  bool operator()( const T& s ) const
  {
    return metaSMT::solve( *s );
  }
};

bool py_solve( const solver& ctx )
{
  return boost::apply_visitor( solve_visitor(), ctx );
}

struct read_value_visitor : public boost::static_visitor<bool>
{
  explicit read_value_visitor( const metaSMT::logic::predicate& pred ) : pred( pred ) {}

  template<typename T>
  bool operator()( const T& s ) const
  {
    return metaSMT::read_value( *s, pred );
  }

private:
  const metaSMT::logic::predicate& pred;
};

bool py_read_value( const solver& ctx, const metaSMT::logic::predicate& pred )
{
  return boost::apply_visitor( read_value_visitor( pred ), ctx );
}

struct read_bv_value_visitor : public boost::static_visitor<unsigned>
{
  explicit read_bv_value_visitor( const metaSMT::logic::QF_BV::bitvector& bv ) : bv( bv ) {}

  template<typename T>
  unsigned operator()( const T& s ) const
  {
    return metaSMT::read_value( *s, bv );
  }

private:
  const metaSMT::logic::QF_BV::bitvector& bv;
};

unsigned py_read_bv_value( const solver& ctx, const metaSMT::logic::QF_BV::bitvector& bv )
{
  return boost::apply_visitor( read_bv_value_visitor( bv ), ctx );
}

// Symbol Table
class smt2_symbol_table
{
public:
  typedef std::map<unsigned, std::string> map;

  std::string operator()( unsigned id )
  {
    map::const_iterator it = _map.find( id );
    if ( it == _map.end() )
    {
      return boost::str( boost::format( "var_%d" ) % id );
    }
    else
    {
      return it->second;
    }
  }

  void insert1( metaSMT::logic::predicate p, const std::string& name )
  {
    _map.insert( std::make_pair( boost::proto::value( p ).id, name ) );
  }

  void insert2( metaSMT::logic::QF_BV::bitvector b, const std::string& name )
  {
    _map.insert( std::make_pair( boost::proto::value( b ).id, name ) );
  }

private:
  map _map;
};

struct set_symbol_table_visitor : public boost::static_visitor<void>
{
  explicit set_symbol_table_visitor( smt2_symbol_table& table ) : table( table ) {}

  void operator()( boost::shared_ptr<smt2_solver>& s ) const
  {
    metaSMT::set_symbol_table( *s, table );
  }

  template<typename T>
  void operator()( T& s ) const
  {
    // do nothing
  }

private:
  smt2_symbol_table& table;
};

void py_set_symbol_table( solver& ctx, smt2_symbol_table& table )
{
  boost::apply_visitor( set_symbol_table_visitor( table ), ctx );
}

void export_solvers()
{
  class_<solver>( "solver" )
    .def( "py_assertion", &py_assertion )
    .def( "solve", &py_solve )
    .def( "read_value", &py_read_value )
    .def( "read_value", &py_read_bv_value )
    .def( "__getitem__", &py_read_value )
    .def( "__getitem__", &py_read_bv_value )
    .def( "set_symbol_table", &py_set_symbol_table )
    ;
#if ENABLE_SOLVER_SWORD
  def( "sword_solver", &make_solver<sword_solver> );
#endif
#if ENABLE_SOLVER_BOOLECTOR
  def( "boolector_solver", &make_solver<boolector_solver> );
#endif
#if ENABLE_SOLVER_Z3
  def( "z3_solver", &make_solver<z3_solver> );
#endif
#if ENABLE_SOLVER_CUDD
  def( "cudd_solver", &make_solver<cudd_solver> );
#endif
#if ENABLE_SOLVER_MINISAT
  def( "minisat_solver", &make_solver<minisat_solver> );
#if ENABLE_SOLVER_AIGER
  def( "minisat_aiger_solver", &make_solver<minisat_aiger_solver> );
#endif
#endif
#if ENABLE_SOLVER_PICOSAT
  def( "picosat_solver", &make_solver<picosat_solver> );
#endif
#if ENABLE_SOLVER_GLUCOSER
  def( "glucoser_executable_solver", &make_solver<glucoser_executable_solver> );
#endif
#if ENABLE_SOLVER_MINISAT_EXECUTABLE
  def( "minisat_executable_solver", &make_solver<minisat_executable_solver> );
#endif
#if ENABLE_SOLVER_PICOSAT_EXECUTABLE
  def( "picosat_executable_solver", &make_solver<picosat_executable_solver> );
#endif
#if ENABLE_SOLVER_PLINGELING_EXECUTABLE
  def( "plingeling_executable_solver", &make_solver<plingeling_executable_solver> );
#endif
#if ENABLE_SOLVER_PRECOSAT_EXECUTABLE
  def( "precosat_executable_solver", &make_solver<precosat_executable_solver> );
#endif
#if ENABLE_SOLVER_SMT2
  def( "smt2_solver", &make_solver<smt2_solver> );
#endif

#if ENABLE_SOLVER_CONSTRAINT
  def( "constraint_solver", &make_solver<constraint_solver> );
#endif

  class_<smt2_symbol_table>( "smt2_symbol_table" )
    .def( "insert", &smt2_symbol_table::insert1 )
    .def( "insert", &smt2_symbol_table::insert2 )
    ;
}
