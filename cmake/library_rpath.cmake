
# Generate an RPATH from all the libraries used by metaSMT.
# If the library is a file use its directory,
# if the library is a target use its location and recurse on
# its dependencies.

macro(add_dependent_libraries)
  foreach( lib ${ARGN})
    if(EXISTS ${lib})
      get_filename_component(libdir ${lib} PATH)
      list(APPEND CMAKE_INSTALL_RPATH ${libdir})
    elseif(lib)
      get_target_property(libpath ${lib} LOCATION)
      get_filename_component(libdir ${libpath} PATH)
      list(APPEND CMAKE_INSTALL_RPATH ${libdir})
      get_target_property(dependent ${lib} IMPORTED_LINK_INTERFACE_LIBRARIES)
      add_dependent_libraries(${dependent})
      get_target_property(dependent ${lib} IMPORTED_LINK_INTERFACE_LIBRARIES_RELEASE)
      add_dependent_libraries(${dependent})
    endif()
  endforeach(lib)
endmacro(add_dependent_libraries)

