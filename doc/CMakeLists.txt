include_directories(../src)

include_directories(${metaSMT_INCLUDES})

if(DOXYGEN_FOUND)
  if(DOXYGEN_DOT_FOUND)
    set(DOXYGEN_HAVE_DOT YES)
  else(DOXYGEN_DOT_FOUND)
    set(DOXYGEN_HAVE_DOT NO)
  endif(DOXYGEN_DOT_FOUND)


  configure_file(Doxyfile.in ${CMAKE_CURRENT_BINARY_DIR}/Doxyfile)
  add_custom_target(doxygen ALL
    ${DOXYGEN_EXECUTABLE} ${CMAKE_CURRENT_BINARY_DIR}/Doxyfile
    WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR} 
    SOURCES ${CMAKE_CURRENT_BINARY_DIR}/Doxyfile
  )
endif(DOXYGEN_FOUND)

