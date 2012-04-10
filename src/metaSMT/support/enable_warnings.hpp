/*
 * This header complements disable_warnings.hpp should only be used in combination with it
 */
#ifdef __GNUC__
#pragma GCC pop_options
#undef _BACKWARD_BACKWARD_WARNING_H
#endif

#ifdef __clang__
#pragma clang diagnostic pop
#undef _BACKWARD_BACKWARD_WARNING_H
#endif
