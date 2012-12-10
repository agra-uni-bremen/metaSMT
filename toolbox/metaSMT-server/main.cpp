#include <iostream>
#include <map>
#include <sstream>
#include <string>

#include <boost/algorithm/string/classification.hpp>
#include <boost/algorithm/string/predicate.hpp>
#include <boost/algorithm/string/split.hpp>
#include <boost/asio.hpp>
#include <boost/bind.hpp>
#include <boost/lexical_cast.hpp>
#include <boost/smart_ptr.hpp>
#include <boost/thread/thread.hpp>

#include <metaSMT/DirectSolver_Context.hpp>
#include <metaSMT/backend/Z3_Backend.hpp>

#include <boost/property_tree/ptree.hpp>
#include <boost/property_tree/json_parser.hpp>

using boost::asio::ip::tcp;

using namespace metaSMT;
using namespace metaSMT::logic;
using namespace metaSMT::logic::QF_BV;
using namespace metaSMT::solver;

typedef boost::shared_ptr<tcp::socket> socket_ptr;

template<typename Context, typename Bitvectors>
typename Context::result_type create_assertion(Context& ctx, const Bitvectors& bitvectors, const boost::property_tree::ptree& pt)
{
  std::string op = pt.get<std::string>("op");

  if (op == "variable")
  {
    return evaluate(ctx, bitvectors.find(pt.get<std::string>("name"))->second);
  }
  else if (op == "integer")
  {
    return evaluate(ctx, bvuint(pt.get<unsigned>("value"), pt.get<unsigned>("width")));
  }
  else if (op == "=")
  {
    typename Context::result_type lhs = create_assertion(ctx, bitvectors, pt.get_child("lhs"));
    typename Context::result_type rhs = create_assertion(ctx, bitvectors, pt.get_child("rhs"));

    return evaluate(ctx, equal(lhs, rhs));
  }
  else
  {
    std::cout << "implement me: " << pt.get<std::string>("op") << std::endl;
  }
}

void session(socket_ptr sock)
{
  DirectSolver_Context<Z3_Backend> solver;
  std::map<std::string, predicate> predicates;
  std::map<std::string, bitvector> bitvectors;

  try
  {
    for (;;)
    {
      std::string ret;

      boost::system::error_code error;
      boost::asio::streambuf b;
      size_t length = read_until(*sock, b, '\n', error);
      if (error == boost::asio::error::eof) break;
      else if (error) throw boost::system::system_error(error);

      std::istream is(&b);
      std::string s;
      std::getline(is, s);
      if (boost::starts_with(s, "new_variable"))
      {
        std::vector<std::string> split;
        boost::split(split, s, boost::algorithm::is_any_of(" "));

        if (split.size() != 2u) {
          ret = "Not enough arguments\n";
        } else {
          predicates.insert(std::make_pair(split[1], new_variable()));
          std::cout << "[INFO] Added predicate " << split[1] << std::endl;
          ret = "OK\n";
        }
      }
      else if (boost::starts_with(s, "new_bitvector"))
      {
        std::vector<std::string> split;
        boost::split(split, s, boost::algorithm::is_any_of(" "));

        if (split.size() != 3u) {
          ret = "Not enough arguments\n";
        } else {
          bitvectors.insert(std::make_pair(split[1], new_bitvector(boost::lexical_cast<unsigned>(split[2]))));
          std::cout << "[INFO] Added bit-vector " << split[1] << " of size " << split[2] << std::endl;
          ret = "OK\n";
        }
      }
      else if (boost::starts_with(s, "assertion"))
      {
        std::cout << s.substr(10u) << std::endl;

        // trim s such that it only contains the json string
        using boost::property_tree::ptree;
        ptree pt;

        std::istringstream in(s.substr(10u));
        boost::property_tree::json_parser::read_json(in, pt);

        assertion(solver, create_assertion(solver, bitvectors, pt));

        ret = "OK\n";
      }
      else if (boost::starts_with(s, "solve"))
      {
        bool result = solve(solver);
        ret = result ? "SAT\n" : "UNSAT\n";
      }
      else if (boost::starts_with(s, "modelvalue"))
      {
        std::vector<std::string> split;
        boost::split(split, s, boost::algorithm::is_any_of(" "));

        if (split.size() != 2u) {
          ret = "Not enough arguments\n";
        } else {
          unsigned value = read_value(solver, bitvectors[split[1]]);
          ret = boost::lexical_cast<std::string>(value) + "\n";
        }
      }
      else
      {
        std::cerr << "I do not understand: " << s;
        ret = "FAIL\n";
      }

      boost::asio::write(*sock, boost::asio::buffer(ret, ret.size()));
    }
  }
  catch (std::exception& e)
  {
    std::cerr << "Exception in thread: " << e.what() << std::endl;
  }
}

void server(boost::asio::io_service& io_service)
{
  tcp::acceptor acceptor(io_service, tcp::endpoint(tcp::v4(), 1313));

  for (;;)
  {
    socket_ptr sock(new tcp::socket(io_service));
    acceptor.accept(*sock);
    boost::thread t(boost::bind(session, sock));
  }
}

int main(int argc, const char *argv[])
{
  try
  {
    boost::asio::io_service io_service;
    server(io_service);
  }
  catch (std::exception& e)
  {
    std::cerr << e.what() << std::endl;
  }

  return 0;
}
