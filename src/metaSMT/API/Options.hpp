#pragma once

#include "../Features.hpp"

namespace metaSMT {
  struct setup_option_map_cmd { typedef void result_type; };
  struct get_option_cmd { typedef std::string result_type; };
  struct set_option_cmd { typedef void result_type; };

  template <typename Context_ >
  std::string get_option( Context_ &ctx, std::string const &key ) {
    BOOST_MPL_ASSERT_MSG(
      ( features::supports<Context_, get_option_cmd>::value )
    , context_does_not_support_get_option_api
    , ()
    );
    return ctx.command(get_option_cmd(), key );
  }

  template <typename Context_ >
  std::string get_option( Context_ &ctx, std::string const &key, std::string const &default_value ) {
    BOOST_MPL_ASSERT_MSG(
      ( features::supports<Context_, get_option_cmd>::value )
    , context_does_not_support_get_option_api
    , ()
    );
    return ctx.command(get_option_cmd(), key, default_value );
  }

  template <typename Context_ >
  void set_option( Context_ &ctx, std::string const &key, std::string const &value ) {
    BOOST_MPL_ASSERT_MSG(
      ( features::supports<Context_, set_option_cmd>::value )
    , context_does_not_support_set_option_api
    , ()
    );
    ctx.command(set_option_cmd(), key, value );
  }
} // metaSMT
