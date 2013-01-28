#include "connection.hpp"

#include <sstream>
#include <string>

#include <boost/algorithm/string/classification.hpp>
#include <boost/algorithm/string/predicate.hpp>
#include <boost/algorithm/string/split.hpp>

#include <boost/asio/read_until.hpp>
#include <boost/asio/streambuf.hpp>
#include <boost/asio/write.hpp>

#include <boost/lexical_cast.hpp>

#include <boost/property_tree/json_parser.hpp>
#include <boost/property_tree/ptree.hpp>

//using namespace metaSMT;
//using namespace metaSMT::logic;
//using namespace metaSMT::logic::QF_BV;
//using namespace metaSMT::solver;

template<typename Context, typename Bitvectors>
typename Context::result_type create_assertion(Context& ctx, const Bitvectors& bitvectors, const boost::property_tree::ptree& pt);

template<typename Context, typename Bitvectors>
typename Context::result_type create_binary_assertion(Context& ctx, const Bitvectors& bitvectors, const boost::property_tree::ptree& pt);

Connection::Connection(socket_ptr socket) :
    sock(socket)
{
}

bool isBinary(const boost::property_tree::ptree& pt)
{
    return pt.find("lhs") != pt.not_found() && pt.find("rhs") != pt.not_found();
}

template<typename Context, typename Bitvectors>
typename Context::result_type create_assertion(Context& ctx, const Bitvectors& bitvectors, const boost::property_tree::ptree& pt)
{
    std::string op = pt.get<std::string>("op");

    if (isBinary(pt)) {
        return create_binary_assertion(ctx, bitvectors, pt);
    } else if (op == "variable") {
        return evaluate(ctx, bitvectors.find(pt.get<std::string>("name"))->second);
    } else if (op == "integer") {
        std::cout << pt.get<signed>("value") << std::endl;
        return evaluate(ctx, metaSMT::logic::QF_BV::bvuint(pt.get<signed>("value"), pt.get<unsigned>("width")));
    } else {
        throw(UnsupportedOperandException(op));
    }
}

template<typename Context, typename Bitvectors>
typename Context::result_type create_binary_assertion(Context& ctx, const Bitvectors& bitvectors, const boost::property_tree::ptree& pt)
{
    std::string op = pt.get<std::string>("op");

    typename Context::result_type lhs = create_assertion(ctx, bitvectors, pt.get_child("lhs"));
    typename Context::result_type rhs = create_assertion(ctx, bitvectors, pt.get_child("rhs"));

    if (op == "equal" || op == "=") {
        return evaluate(ctx, metaSMT::logic::equal(lhs, rhs));
    } else if (op == "nequal" || op == "!=") {
        return evaluate(ctx, metaSMT::logic::nequal(lhs, rhs));
    } else if (op == "implies" || op == "=>") {
        return evaluate(ctx, metaSMT::logic::implies(lhs, rhs));
    } else if (op == "and" || op == "&&") {
        return evaluate(ctx, metaSMT::logic::And(lhs, rhs));
    } else if (op == "nand") {
        return evaluate(ctx, metaSMT::logic::Nand(lhs, rhs));
    } else if (op == "or" || op == "||") {
        return evaluate(ctx, metaSMT::logic::Or(lhs, rhs));
    } else if (op == "nor") {
        return evaluate(ctx, metaSMT::logic::Nor(lhs, rhs));
    } else if (op == "xor") {
        return evaluate(ctx, metaSMT::logic::Xor(lhs, rhs));
    } else if (op == "xnor") {
        return evaluate(ctx, metaSMT::logic::Xnor(lhs, rhs));
    }


    else if (op == "bvand" || op == "&") {
        return evaluate(ctx, metaSMT::logic::QF_BV::bvand(lhs, rhs));
    } else if (op == "bvnand") {
        return evaluate(ctx, metaSMT::logic::QF_BV::bvnand(lhs, rhs));
    } else if (op == "bvor" || op == "|") {
        return evaluate(ctx, metaSMT::logic::QF_BV::bvor(lhs, rhs));
    } else if (op == "bvnor") {
        return evaluate(ctx, metaSMT::logic::QF_BV::bvnor(lhs, rhs));
    } else if (op == "bvxor" || op == "^") {
        return evaluate(ctx, metaSMT::logic::QF_BV::bvxor(lhs, rhs));
    } else if (op == "bvxnor") {
      return evaluate(ctx, metaSMT::logic::QF_BV::bvxnor(lhs, rhs));

    } else if (op == "bvadd" || op == "+") {
        return evaluate(ctx, metaSMT::logic::QF_BV::bvadd(lhs, rhs));
    } else if (op == "bvmul" || op == "*") {
        return evaluate(ctx, metaSMT::logic::QF_BV::bvmul(lhs, rhs));
    } else if (op == "bvsub" || op == "-") {
        return evaluate(ctx, metaSMT::logic::QF_BV::bvsub(lhs, rhs));
    } else if (op == "bvudiv") {
        return evaluate(ctx, metaSMT::logic::QF_BV::bvudiv(lhs, rhs));
    } else if (op == "bvurem") {
        return evaluate(ctx, metaSMT::logic::QF_BV::bvurem(lhs, rhs));
    } else if (op == "bvsdiv") {
        return evaluate(ctx, metaSMT::logic::QF_BV::bvsdiv(lhs, rhs));
    } else if (op == "bvsrem") {
        return evaluate(ctx, metaSMT::logic::QF_BV::bvsrem(lhs, rhs));

    } else if (op == "bvcomp" || op == "==") {
        return evaluate(ctx, metaSMT::logic::QF_BV::bvcomp(lhs, rhs));

    } else if (op == "bvslt") {
        return evaluate(ctx, metaSMT::logic::QF_BV::bvslt(lhs, rhs));
    } else if (op == "bvsgt") {
        return evaluate(ctx, metaSMT::logic::QF_BV::bvsgt(lhs, rhs));
    } else if (op == "bvsle") {
        return evaluate(ctx, metaSMT::logic::QF_BV::bvsle(lhs, rhs));
    } else if (op == "bvsge") {
        return evaluate(ctx, metaSMT::logic::QF_BV::bvsge(lhs, rhs));

    } else if (op == "bvult") {
        return evaluate(ctx, metaSMT::logic::QF_BV::bvult(lhs, rhs));
    } else if (op == "bvugt") {
        return evaluate(ctx, metaSMT::logic::QF_BV::bvugt(lhs, rhs));
    } else if (op == "bvule") {
        return evaluate(ctx, metaSMT::logic::QF_BV::bvule(lhs, rhs));
    } else if (op == "bvuge") {
        return evaluate(ctx, metaSMT::logic::QF_BV::bvuge(lhs, rhs));
    } else if (op == "bvshl") {
        return evaluate(ctx, metaSMT::logic::QF_BV::bvshl(lhs, rhs));
    } else if (op == "bvshr") {
        return evaluate(ctx, metaSMT::logic::QF_BV::bvshr(lhs, rhs));
    } else if (op == "bvashr") {
        return evaluate(ctx, metaSMT::logic::QF_BV::bvashr(lhs, rhs));

    } else if (op == "concat" || op == "++") {
        return evaluate(ctx, metaSMT::logic::QF_BV::concat(lhs, rhs));
    } else {
        throw(UnsupportedOperandException(op));
    }
}

void Connection::start()
{
    std::cout << "New connection" << std::endl;

    boost::asio::streambuf b;
    for (;;)
    {
        std::string ret;
        try
        {
            boost::system::error_code error;
            size_t length = read_until(*sock, b, '\n', error);
            if (error == boost::asio::error::eof) break;
            else if (error) throw boost::system::system_error(error);

            std::istream is(&b);
            std::string s;
            std::getline(is, s);
            s.erase(s.find_last_not_of(" \n\r\t") + 1);
            if (boost::starts_with(s, "new_variable"))
            {
                std::vector<std::string> split;
                boost::split(split, s, boost::algorithm::is_any_of(" "));

                if (split.size() != 2u) {
                    ret = "Not enough arguments\n";
                } else {
                    predicates.insert(std::make_pair(split[1], metaSMT::logic::new_variable()));
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
                    bitvectors.insert(std::make_pair(split[1], metaSMT::logic::QF_BV::new_bitvector(boost::lexical_cast<unsigned>(split[2]))));
                    std::cout << "[INFO] Added bit-vector " << split[1] << " of size " << split[2] << std::endl;
                    ret = "OK\n";
                }
            }
            else if (boost::starts_with(s, "assertion"))
            {
                std::cout << s.substr(10u) << std::endl;

                // trim s such that it only contains the json string
                boost::property_tree::ptree pt;

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
            } else {
                throw UnsupportedCommandException(s);
            }
        } catch (UnsupportedOperandException& e) {
            ret = "FAIL\n";
            std::cout << "Unsupported operand: " << e.what() << std::endl;
        } catch (UnsupportedCommandException& e) {
            ret = "FAIL\n";
            std::cout << "Unsupported command: " << e.what() << std::endl;
        } catch (std::exception& e) {
            ret = "FAIL\n";
            std::cerr << "Exception in thread: " << e.what() << std::endl;
        }

        try {
            boost::asio::write(*sock, boost::asio::buffer(ret, ret.size()));
        } catch (std::exception& e) {
            std::cerr << "Exception: " << e.what() << std::endl;
            break;
        }
    }
    std::cout << "Closing connection" << std::endl;
    sock->close();
}
