file(GLOB toolbox_entries ${CMAKE_CURRENT_SOURCE_DIR}/*/)


## helper funtion to conditionally build a tool
function (add_tool_executable name )
  cmake_parse_arguments(_req "" "" "SOURCES;REQUIRES;PROPERTIES;ARGS;LIBRARIES;ENV" ${ARGN})

  set(_req_all 1)

  foreach( _req ${_req_REQUIRES} )
    if(NOT ${_req} )
      set(_req_all 0)
    endif(NOT ${_req} )
  endforeach( _req )

  if(_req_all)
    add_executable(${name} ${_req_SOURCES})
    target_link_libraries(${name} metaSMT)
    if(_req_LIBRARIES)
      target_link_libraries(${name} ${_req_LIBRARIES})
    endif()
    if(_req_PROPERTIES)
      set_target_properties(${name} PROPERTIES ${_req_PROPERTIES})
    endif()

    set(${name}_ENABLED TRUE PARENT_SCOPE)
  endif(_req_all)
endfunction(add_tool_executable)

include_directories(${metaSMT_SOURCE_DIR}/src ${metaSMT_INCLUDES})
add_definitions(${metaSMT_CXXFLAGS})

foreach(entry ${toolbox_entries})
  if(IS_DIRECTORY ${entry})
    get_filename_component(_name ${entry} NAME)
    if(EXISTS ${entry}/CMakeLists.txt)
      add_subdirectory(${entry})
    else()
      file(GLOB _sources ${entry}/*.cc ${entry}/*.cpp)
      if( _sources )
        add_tool_executable(${_name}.auto SOURCES ${_sources})
      endif()
    endif()
  endif()
endforeach(${entry})
