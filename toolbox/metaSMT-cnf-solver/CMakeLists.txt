add_tool_executable( metaSMT-cnf-solver
  SOURCES
    main.cpp
  REQUIRES
    PicoSAT_FOUND
    Boost_ASIO_LIBRARY
)

