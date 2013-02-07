#include "connection.hpp"

#include <metaSMT/backend/Z3_Backend.hpp>

bool is_unary(const boost::property_tree::ptree& pt)
{
    return pt.find("operand") != pt.not_found();
}

bool is_binary(const boost::property_tree::ptree& pt)
{
    return pt.find("lhs") != pt.not_found() && pt.find("rhs") != pt.not_found();
}

void new_connection(socket_ptr socket)
{
    Connection<metaSMT::solver::Z3_Backend> connection(socket);
    connection.start();
}
