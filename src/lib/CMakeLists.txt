add_library(metaSMT STATIC
  _var_id.cpp
  expression_generator.cpp
)
target_link_libraries(metaSMT ${metaSMT_LIBS})
if( CMAKE_COMPILER_IS_GNUCC OR ("${CMAKE_CXX_COMPILER_ID}" MATCHES Clang))
set_target_properties(metaSMT PROPERTIES COMPILE_FLAGS "-fPIC -g0 -O3")
endif()


install(TARGETS metaSMT 
  EXPORT metaSMT
  LIBRARY DESTINATION lib
  RUNTIME DESTINATION bin
  ARCHIVE DESTINATION lib
)
