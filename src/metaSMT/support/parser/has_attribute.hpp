#pragma once

// lazily typed

namespace metaSMT {
  namespace support {
    namespace detail {
      template < typename Attr >
      struct HasAttributeVisitor {
        HasAttributeVisitor(bool &found,
                            bool &has_attribute,
                            std::string const &name)
          : found(found)
          , has_attribute(has_attribute)
          , name(name)
        {}

        template < typename Pair >
        void operator()( Pair const & ) {
          typedef typename Pair::first Tag;
          typedef typename Pair::second Name;
          if ( !found &&
               mpl::c_str<Name>::value == name ) {          
            found = true;
            has_attribute = boost::is_same<typename Tag::attribute, Attr>::value;
          }
        }

        bool &found;
        bool &has_attribute;
        std::string const name;
      }; // HasAttributeVisitor
    } // detail

    template < typename Attr >
    bool has_attribute( std::string const &name ) {
      bool found = false;
      bool has_attribute = false;
      detail::HasAttributeVisitor<Attr> visitor(found, has_attribute, name);
      mpl::for_each< SMT_NameMap >( visitor );
      assert( found );
      return has_attribute;
    }
  } // support
} // metaSMT
