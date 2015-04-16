
# Generate an RPATH from all the libraries used by metaSMT.
# If the library is a file use its directory,
# if the library is a target use its location and recurse on
# its dependencies.

macro( _recursive_collect_rpath )
  foreach( lib ${ARGN})
    if(EXISTS ${lib})
      get_filename_component(libdir ${lib} PATH)
      list(APPEND _rpath ${libdir})
    elseif(TARGET ${lib})
      get_target_property(libpath ${lib} LOCATION)
      get_filename_component(libdir ${libpath} PATH)
      list(APPEND _rpath ${libdir})
      get_target_property(dependent ${lib} IMPORTED_LINK_INTERFACE_LIBRARIES)
      _recursive_collect_rpath(${dependent})
      get_target_property(dependent ${lib} IMPORTED_LINK_INTERFACE_LIBRARIES_RELEASE)
      _recursive_collect_rpath(${dependent})
    endif()
  endforeach()
endmacro( )

function(add_dependent_libraries)
  set( _rpath "")

  _recursive_collect_rpath( ${ARGN} )

  list( SORT _rpath )
  list( REMOVE_DUPLICATES _rpath )

  set( CMAKE_INSTALL_RPATH ${CMAKE_INSTALL_RPATH} ${_rpath} PARENT_SCOPE)
endfunction()

