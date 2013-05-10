add_tool_executable( metaSMT-server
  SOURCES
    main.cpp
    connection.cpp
  REQUIRES
    Boost_FOUND
    Z3_FOUND
  LIBRARIES
    pthread
    boost_system
    boost_thread
)
