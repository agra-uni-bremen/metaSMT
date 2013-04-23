#include "connection.hpp"

#include <list>

#include <boost/thread/thread.hpp>

#include <metaSMT/BitBlast.hpp>
#include <metaSMT/backend/Boolector.hpp>
#include <metaSMT/backend/SAT_Clause.hpp>
#include <metaSMT/backend/PicoSAT.hpp>
#include <metaSMT/backend/Z3_Backend.hpp>

int ConnectionBase::init()
{
    return pipe(fd_c2p) != -1 && pipe(fd_p2c) != -1;
}

std::string ConnectionBase::child_read_command()
{
    return read_command(fd_p2c[0]);
}

void ConnectionBase::child_write_command(std::string s)
{
    write_command(fd_c2p[1], s);
}

std::string ConnectionBase::parent_read_command()
{
    return read_command(fd_c2p[0]);
}

void ConnectionBase::parent_write_command(std::string s)
{
    write_command(fd_p2c[1], s);
}

std::string ConnectionBase::read_command(int fd)
{
    std::string s;
    char buf[1];
    do {
        read(fd, buf, 1);
        s += buf[0];
    } while (buf[0] != '\n');

    s.erase(s.find_last_not_of(" \n\r\t") + 1);
    return s;
}

void ConnectionBase::write_command(int fd, std::string s)
{
    s += "\n";
    write(fd, s.c_str(), s.length());
}

bool is_unary(const boost::property_tree::ptree& pt)
{
    return pt.find("operand") != pt.not_found();
}

bool is_binary(const boost::property_tree::ptree& pt)
{
    return pt.find("lhs") != pt.not_found() && pt.find("rhs") != pt.not_found();
}

std::string next_line(socket_ptr socket, boost::asio::streambuf& buffer)
{
    boost::system::error_code error;
    size_t length = read_until(*socket, buffer, '\n', error);
    //if (error == boost::asio::error::eof) break;
    /*else*/ if (error) throw boost::system::system_error(error);

    std::istream is(&buffer);
    std::string s;
    std::getline(is, s);
    s.erase(s.find_last_not_of(" \n\r\t") + 1);

    return s;
}

void new_connection(socket_ptr socket)
{
    std::cout << "New connection" << std::endl;

    try {
        std::string solvers = "0 z3; 1 picosat; 2 boolector\n";
        boost::asio::write(*socket, boost::asio::buffer(solvers, solvers.size()));

        boost::asio::streambuf buffer;
        std::string str;
        std::string ret;

        std::list<ConnectionBase*> connections;

        //select solvers
        while (true) {
            ret = "OK\n";
            str = next_line(socket, buffer);
            int solver;
            try {
                solver = boost::lexical_cast<unsigned>(str);
            } catch (boost::bad_lexical_cast e) {
                break;
            }

            switch(solver) {
            case 0:
                connections.push_back(new Connection<metaSMT::solver::Z3_Backend>());
                break;
            case 1:
                connections.push_back(new Connection<metaSMT::BitBlast<metaSMT::SAT_Clause<metaSMT::solver::PicoSAT> > >());
                break;
            case 2:
                connections.push_back(new Connection<metaSMT::solver::Boolector>());
                break;
            default:
                ret = "FAIL unsupported solver\n";
            }

            boost::asio::write(*socket, boost::asio::buffer(ret, ret.size()));
        }

        //receive commands
        for (std::list<ConnectionBase*>::iterator i = connections.begin(); i != connections.end(); i++) {
            if (!(*i)->init()) {
                ret = "Could not create pipe for IPC.\n";
                std::cout << ret << std::endl;
                boost::asio::write(*socket, boost::asio::buffer(ret, ret.size()));
                return;
            }
            pid_t pid = fork();
            if (pid == -1) {
                ret = "Could not fork new process.\n";
                std::cout << ret << std::endl;
                boost::asio::write(*socket, boost::asio::buffer(ret, ret.size()));
                return;
            } else if (pid) {
                //PARENT PROCESS
            } else {
                //CHILD PROCESS
                (*i)->start();
                return;
            }
        }

        while (true) {
            for (std::list<ConnectionBase*>::iterator i = connections.begin(); i != connections.end(); i++) {
                (*i)->parent_write_command(str);
            }

            std::vector<std::string> answers(connections.size());
            int n = 0;
            for (std::list<ConnectionBase*>::iterator i = connections.begin(); i != connections.end(); i++) {
                answers[n++] = (*i)->parent_read_command();
            }

            //return a FAIL if not all answers are the same, otherwise return the consistent answer
            ret = answers[0] + "\n";
            for (int n = 0; n < answers.size() -1; n++) {
                if (answers[n] != answers[n+1]) {
                    ret = "FAIL inconsistent solver behavior\n";
                    break;
                }
            }

            boost::asio::write(*socket, boost::asio::buffer(ret, ret.size()));
            str = next_line(socket, buffer);
        }
    } catch (std::exception& e) {
        std::cout << "Closing connection: " << e.what() << std::endl;
        socket->close();
        return;
    }
}
