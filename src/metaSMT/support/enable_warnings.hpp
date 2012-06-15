/*
 * This header complements disable_warnings.hpp should only be used in combination with it
 */
#ifdef __GNUC__
# if __GNUC__ >= 4 and __GNUC_MINOR__ > 4
// this makes gcc 4.4 corrupt executables and cause random segfaults
#pragma GCC pop_options
#undef _BACKWARD_BACKWARD_WARNING_H
#endif
#endif

#ifdef __clang__
#pragma clang diagnostic pop
#undef _BACKWARD_BACKWARD_WARNING_H
#endif
