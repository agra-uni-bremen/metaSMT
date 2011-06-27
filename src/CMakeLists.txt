
add_subdirectory(lib)
install(DIRECTORY metaSMT 
  DESTINATION include/
  FILES_MATCHING PATTERN "*.hpp"
)

# vim: ft=cmake:ts=2:sw=2:expandtab
