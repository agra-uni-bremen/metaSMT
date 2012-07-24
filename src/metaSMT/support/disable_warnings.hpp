/*
 * This header may be included before including system or library headers that
 * emits an  warning.
 *
 * IMPORTANT: Do not forget to include enable_warnings.hpp after including the
 * external headers to re-enable warnings again.
 */
#ifdef __clang__
#define _BACKWARD_BACKWARD_WARNING_H
#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Wstrict-aliasing"
#pragma clang diagnostic ignored "-Wunused-variable"
#pragma clang diagnostic ignored "-Wreturn-type"
#pragma clang diagnostic ignored "-Wsign-compare"
#pragma clang diagnostic ignored "-Wunknown-pragmas"
#pragma clang diagnostic ignored "-Wdelete-non-virtual-dtor"
#pragma clang diagnostic ignored "-Wparentheses-equality"
#pragma clang diagnostic ignored "-Wlogical-op-parentheses"
#endif


#ifdef __GNUC__
# if __GNUC__ >= 4 and __GNUC_MINOR__ > 4
// with this definitions gcc 4.4 creates executables with random segfaults
#define _BACKWARD_BACKWARD_WARNING_H
#pragma GCC push_options
#pragma GCC diagnostic ignored "-Wstrict-aliasing"
#pragma GCC diagnostic ignored "-Wunused-variable"
#pragma GCC diagnostic ignored "-Wreturn-type"
#pragma GCC diagnostic ignored "-Wsign-compare"
#pragma GCC diagnostic ignored "-Wparentheses"
#endif
#endif

