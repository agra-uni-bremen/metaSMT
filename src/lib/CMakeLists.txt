add_library(metaSMT STATIC _var_id.cpp)
target_link_libraries(metaSMT ${metaSMT_LIBS})
set_target_properties(metaSMT PROPERTIES COMPILE_FLAGS "-fPIC")

install(TARGETS metaSMT 
  EXPORT metaSMT
  LIBRARY DESTINATION lib
  RUNTIME DESTINATION bin
  ARCHIVE DESTINATION lib
)
