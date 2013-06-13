add_tool_executable( metaSMT-server
  SOURCES
    main.cpp
    connection.cpp
  REQUIRES
    Boost_FOUND
    Boolector_FOUND
    PicoSAT_FOUND
    Z3_FOUND
  LIBRARIES
    pthread
    ${Boost_SYSTEM_LIBRARY}
    ${Boost_THREAD_LIBRARY}
)
