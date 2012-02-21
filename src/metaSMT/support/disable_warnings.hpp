/*
 * This header may be included before including system or library headers that
 * emits an  warning.
 *
 * IMPORTANT: Do not forget to include enable_warnings.hpp after including the
 * external headers to re-enable warnings again.
 */
#ifdef __GNUC__
#pragma GCC push_options
#pragma GCC diagnostic ignored "-Wstrict-aliasing"
#pragma GCC diagnostic ignored "-Wunused-variable"
#pragma GCC diagnostic ignored "-Wreturn-type"
#endif
