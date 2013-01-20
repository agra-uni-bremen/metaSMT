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

#include <boost/property_tree/ptree.hpp>
#include <boost/property_tree/json_parser.hpp>

//using namespace metaSMT;
//using namespace metaSMT::logic;
//using namespace metaSMT::logic::QF_BV;
//using namespace metaSMT::solver;

Connection::Connection(socket_ptr socket) :
    sock(socket)
{
}

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
        return evaluate(ctx, metaSMT::logic::QF_BV::bvuint(pt.get<unsigned>("value"), pt.get<unsigned>("width")));
    }
    else if (op == "=")
    {
        typename Context::result_type lhs = create_assertion(ctx, bitvectors, pt.get_child("lhs"));
        typename Context::result_type rhs = create_assertion(ctx, bitvectors, pt.get_child("rhs"));

        return evaluate(ctx, metaSMT::logic::equal(lhs, rhs));
    }
    else
    {
        std::cout << "implement me: " << pt.get<std::string>("op") << std::endl;
    }
}

void Connection::start()
{
    try
    {
        boost::asio::streambuf b;
        for (;;)
        {
            std::string ret;

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
            }
            else
            {
                std::cerr << "I don't understand: " << s << std::endl;
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
