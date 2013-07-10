#pragma once
#include "../../support/index/Logics.hpp"
#include "../../support/SMT_Tag_Mapping.hpp"
#include <boost/mpl/string.hpp>
#include <boost/mpl/for_each.hpp>

namespace metaSMT {
  namespace support {
    namespace idx {
      namespace mpl = boost::mpl;

      namespace detail {
        struct IndexVisitor {
          IndexVisitor(bool &found,
                       logic::index &idx,
                       std::string const &name)
            : found(found)
            , idx(idx)
            , name(name)
          {}

          template < typename Pair >
          void operator()( Pair const & ) {
            typedef typename Pair::first Tag;
            typedef typename Pair::second Name;
            if ( !found &&
                 mpl::c_str<Name>::value == name ) {          
              found = true;
              idx = logic::Index<Tag>::value;
            }
          }
          
          bool &found;
          logic::index &idx;
          std::string const name;
        }; // IndexVisitor
      } // detail

      inline boost::optional< logic::index >
      get_index( std::string const &name ) {
        bool found = false;
        logic::index idx = 0;
        detail::IndexVisitor visitor(found, idx, name);
        mpl::for_each< SMT_NameMap >( visitor );
        if ( found ) {
          return boost::optional< logic::index >(idx);
        }
        else {
          return boost::optional< logic::index >();
        }
      } // get_index
    } // idx
  } // support
} // metaSMT
