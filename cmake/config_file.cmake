#
# metaSMT generates a CMake config file, that can be included by
# other projects to find use metaSMT. This can be done with
#
#  find_package( metaSMT REQUIRED )
#  include_directories( ${metaSMT_INCLUDE_DIR} )
#  target_link_libraries( my_target metaSMT )
#
# To be able to use the configured backends in other projects metaSMT
# invokes find_package from its config file and passes the path used
# by metaSMT as a hint to the call. Other projects therefore by default
# use the same backends that metaSMT used.

###### Functions #####
#
# Function to add a package to the metaSMT config file:
#
# config_find( package path )
#
#   package - the name of the package to search
#   path    - the path to search for the package from the config file

function( config_find package path)
  set(_metaSMT_EXTERNAL_FIND
    "${_metaSMT_EXTERNAL_FIND}
find_package(${package} QUIET PATHS ${path})"
    PARENT_SCOPE )
endfunction(config_find)

function(_append_real_library lib lib_var)
  if ( TARGET ${lib} )
    get_target_property(_lib_location ${lib} LOCATION )
    set( _reallib "${_lib_location}")

  elseif (EXISTS ${lib})
    set( _reallib "${lib}")

  else ()
    set( _reallib "-l${lib}")

  endif ()
  set( ${lib_var} "${${lib_var}} ${_reallib}" PARENT_SCOPE)
endfunction()

function( generate_config_files )

  list(INSERT metaSMT_INCLUDES 0 ${CMAKE_INSTALL_PREFIX}/include)

  set(metaSMT_MLIBS "")

  foreach( lib  ${metaSMT_LIBS} )
    _append_real_library( ${lib} metaSMT_MLIBS )
  endforeach(lib)
  set( metaSMT_MLIBS "${CMAKE_INSTALL_PREFIX}/lib/libmetaSMT.a ${metaSMT_MLIBS}")

  string(REPLACE ";" " -I" metaSMT_MINCLUDES ";${metaSMT_INCLUDES}")

  ## create metaSMT CMake config file
  configure_file(
      ${PROJECT_SOURCE_DIR}/cmake/metaSMTConfig.cmake.in
      ${PROJECT_BINARY_DIR}/metaSMTConfig.cmake
      @ONLY
  )
  ## create libmetaSMT config file for internal use
  configure_file(
      ${PROJECT_SOURCE_DIR}/cmake/metaSMT.cmake.in
      ${PROJECT_BINARY_DIR}/metaSMT.cmake
      @ONLY
  )

  ## export target with install
  INSTALL( FILES
    ${PROJECT_BINARY_DIR}/metaSMTConfig.cmake
  	DESTINATION share/metaSMT)
  install(EXPORT metaSMT DESTINATION share/metaSMT)

  ## create metaSMT CMake make config file
  configure_file(
      ${PROJECT_SOURCE_DIR}/cmake/metaSMT.makefile.in
      ${PROJECT_BINARY_DIR}/metaSMT.makefile
      @ONLY
  )
  INSTALL( FILES
    ${PROJECT_BINARY_DIR}/metaSMT.makefile
  	DESTINATION ${metaSMT_CONFIG_DIR})

  ## create metaSMT pkgconfig make config file
  configure_file(
      ${PROJECT_SOURCE_DIR}/cmake/metaSMT.pc.in
      ${PROJECT_BINARY_DIR}/metaSMT.pc
      @ONLY
  )
  INSTALL( FILES
    ${PROJECT_BINARY_DIR}/metaSMT.pc
  	DESTINATION lib/pkgconfig/)

endfunction( generate_config_files )


# initial values
set(_metaSMT_EXTERNAL_FIND "")

