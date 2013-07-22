#include <metaSMT/support/default_visitation_unrolling_limit.hpp>
#include "Connection.hpp"
#include <boost/asio/ip/tcp.hpp>
#include <boost/thread/thread.hpp>
#include <boost/smart_ptr.hpp>
#include <iostream>

namespace asio = boost::asio;
using asio::ip::tcp;

void server(asio::io_service &io_service) {
  int const port = 1313;
  tcp::acceptor acceptor(io_service, tcp::endpoint(tcp::v4(), port));
  std::cout << "metaSMT-server started" << std::endl;
  std::cout << "Listening on port " << port << std::endl;

  for (;;) {
    typedef boost::shared_ptr<boost::asio::ip::tcp::socket> SocketPtr;
    SocketPtr sock(new tcp::socket(io_service));
    acceptor.accept(*sock);
    boost::thread t(boost::bind(Connection::new_connection, sock));
  }
}

int main(int argc, const char *argv[]) {
  try {
    asio::io_service io_service;
    server(io_service);
  }
  catch (std::exception &e) {
    std::cerr << e.what() << std::endl;
  }
  return 0;
}
