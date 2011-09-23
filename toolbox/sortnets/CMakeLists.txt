add_tool_executable( sortnets_logic
  SOURCES
    logic.cpp
  REQUIRES
    Boolector_FOUND
    SWORD_FOUND
  LIBRARIES
    ${Boost_IOSTREAMS_LIBRARY}
)

