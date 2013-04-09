#ifndef CONNECTION_HPP
#define CONNECTION_HPP

#include <map>

#include <boost/asio/ip/tcp.hpp>
#include <boost/smart_ptr.hpp>

#include <boost/property_tree/json_parser.hpp>
#include <boost/property_tree/ptree.hpp>

#include <metaSMT/DirectSolver_Context.hpp>

#include <sstream>
#include <string>

#include <boost/algorithm/string/classification.hpp>
#include <boost/algorithm/string/predicate.hpp>
#include <boost/algorithm/string/split.hpp>

#include <boost/asio/read_until.hpp>
#include <boost/asio/streambuf.hpp>
#include <boost/asio/write.hpp>

#include <boost/lexical_cast.hpp>

typedef boost::shared_ptr<boost::asio::ip::tcp::socket> socket_ptr;

bool is_unary(const boost::property_tree::ptree& pt);
bool is_binary(const boost::property_tree::ptree& pt);
std::string next_line(socket_ptr socket, boost::asio::streambuf& buffer);
void new_connection(socket_ptr socket);


class UnsupportedOperatorException : public std::runtime_error
{
public:
    UnsupportedOperatorException(std::string op) : std::runtime_error(op) {}
};

class UnsupportedCommandException : public std::runtime_error
{
public:
    UnsupportedCommandException(std::string command) : std::runtime_error(command) {}
};

class UnsupportedSolverException : public std::runtime_error
{
public:
    UnsupportedSolverException(std::string solver) : std::runtime_error(solver) {}
};

class UndefinedVariableException : public std::runtime_error
{
public:
    UndefinedVariableException(std::string variable) : std::runtime_error("Cannot find variable: " + variable) {}
};


template<typename Context, typename Predicates, typename Bitvectors>
typename Context::result_type create_unary_assertion(Context& ctx, const Predicates& predicates, const Bitvectors& bitvectors, const boost::property_tree::ptree& pt);

template<typename Context, typename Predicates, typename Bitvectors>
typename Context::result_type create_binary_assertion(Context& ctx, const Predicates& predicates, const Bitvectors& bitvectors, const boost::property_tree::ptree& pt);

template<typename Context, typename Predicates, typename Bitvectors>
typename Context::result_type create_assertion(Context& ctx, const Predicates& predicates, const Bitvectors& bitvectors, const boost::property_tree::ptree& pt)
{
    std::string op = pt.get<std::string>("op");

    if (is_binary(pt)) {
        return create_binary_assertion(ctx, predicates, bitvectors, pt);
    } else if (is_unary(pt)) {
        return create_unary_assertion(ctx, predicates, bitvectors, pt);
    } else if (op == "variable") {
        std::string name = pt.get<std::string>("name");

        typename Predicates::const_iterator itp = predicates.find(name);
        if (itp != predicates.end()) {
            return evaluate(ctx, itp->second);
        } else {
            typename Bitvectors::const_iterator itb = bitvectors.find(name);
            if (itb != bitvectors.end()) {
                return evaluate(ctx, itb->second);
            } else {
                throw(UndefinedVariableException(name));
            }
        }
    } else if (op == "integer") {
//        std::cout << pt.get<signed>("value") << std::endl;
        return evaluate(ctx, metaSMT::logic::QF_BV::bvuint(pt.get<signed>("value"), pt.get<unsigned>("width")));
    } else {
        throw(UnsupportedOperatorException(op));
    }
}

template<typename Context, typename Predicates, typename Bitvectors>
typename Context::result_type create_unary_assertion(Context& ctx, const Predicates& predicates, const Bitvectors& bitvectors, const boost::property_tree::ptree& pt)
{
    std::string op = pt.get<std::string>("op");

    typename Context::result_type operand = create_assertion(ctx, predicates, bitvectors, pt.get_child("operand"));
    if (op == "not") {
        return evaluate(ctx, metaSMT::logic::Not(operand));
    }

    else if (op == "bvnot") {
        return evaluate(ctx, metaSMT::logic::QF_BV::bvnot(operand));
    } else if (op == "bvneg") {
        return evaluate(ctx, metaSMT::logic::QF_BV::bvneg(operand));
    } else {
        throw(UnsupportedOperatorException(op));
    }
}

template<typename Context, typename Predicates, typename Bitvectors>
typename Context::result_type create_binary_assertion(Context& ctx, const Predicates& predicates, const Bitvectors& bitvectors, const boost::property_tree::ptree& pt)
{
    std::string op = pt.get<std::string>("op");

    typename Context::result_type lhs = create_assertion(ctx, predicates, bitvectors, pt.get_child("lhs"));
    typename Context::result_type rhs = create_assertion(ctx, predicates, bitvectors, pt.get_child("rhs"));

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
        throw(UnsupportedOperatorException(op));
    }
}

class ConnectionBase
{
public:
    virtual void start() = 0;
};

template<typename Context> class Connection : public ConnectionBase
{
public:
    Connection(socket_ptr socket, boost::asio::streambuf* buffer) :
    sock(socket),
    b(buffer) {}

    void start()
    {
        std::cout << "New connection" << std::endl;

        for (;;)
        {
            std::string ret;
            try
            {
                std::string s = next_line(sock, *b);
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

                    assertion(solver, create_assertion(solver, predicates, bitvectors, pt));

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
                        const std::string& name = split.at(1u);
                        std::map<std::string, metaSMT::logic::predicate>::const_iterator itp = predicates.find(name);
                        if (itp != predicates.end()) {
                            ret = boost::lexical_cast<std::string>(read_value(solver, itp->second)) + "\n";
                        } else {
                            std::map<std::string, metaSMT::logic::QF_BV::bitvector>::const_iterator itb = bitvectors.find(name);
                            if (itb != bitvectors.end()) {
                                ret = boost::lexical_cast<std::string>(read_value(solver, itb->second)) + "\n";
                            } else {
                                ret = "Unknown variable: " + name + "\n";
                            }
                        }
                    }
                } else {
                    throw UnsupportedCommandException(s);
                }
            } catch (UnsupportedOperatorException& e) {
                ret = "FAIL\n";
                std::cout << "Unsupported operator: " << e.what() << std::endl;
            } catch (UnsupportedCommandException& e) {
                ret = "FAIL\n";
                std::cout << "Unsupported command: " << e.what() << std::endl;
            } catch (std::exception& e) {
                ret = "FAIL\n";
                std::cerr << "Exception in thread: " << e.what() << std::endl;
            } catch (...) {
                ret = "FAIL\n";
                std::cerr << "Exception in solver" << std::endl;
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

private:
    socket_ptr sock;
    boost::asio::streambuf* b;

    metaSMT::DirectSolver_Context<Context> solver;
    std::map<std::string, metaSMT::logic::predicate> predicates;
    std::map<std::string, metaSMT::logic::QF_BV::bitvector> bitvectors;
};

#endif
