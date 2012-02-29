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

  set(doc_name "metaSMT-docs-${metaSMT_VERSION}") 

  add_custom_target(package_doxygen
    COMMAND ${CMAKE_COMMAND} -E copy_directory html "${doc_name}" 
    COMMAND ${CMAKE_COMMAND} -E tar zcf "${PROJECT_BINARY_DIR}/${doc_name}.tar.gz" "${doc_name}"
    COMMAND ${CMAKE_COMMAND} -E tar jcf "${PROJECT_BINARY_DIR}/${doc_name}.tar.bz2" "${doc_name}"
    WORKING_DIRECTORY "${CMAKE_CURRENT_BINARY_DIR}"
    DEPENDS doxygen
  )
endif(DOXYGEN_FOUND)

