#pragma once

#include "SMT_Graph.hpp"
#include "SMT_Tag_Mapping.hpp"
#include <boost/utility/enable_if.hpp>
#include <boost/foreach.hpp>
#include <boost/dynamic_bitset.hpp>

#include <ostream>
#include <set>

namespace metaSMT {

  namespace predtags = ::metaSMT::logic::tag;
  namespace bvtags = ::metaSMT::logic::QF_BV::tag;
  namespace arraytags = ::metaSMT::logic::Array::tag;
  namespace mpl = boost::mpl;

  void print_SMT_Expression(std::ostream &outfile,
                            SMT_Graph const &g,
                            SMT_Expression const &v);

  struct Vertex_Printer : public boost::static_visitor<void> {
  public:
    Vertex_Printer(std::ostream &outfile,
                   SMT_Graph const &g,
                   SMT_Expression const &v)
      : outfile_(outfile),
        g_(g), v_(v)
    {}

    inline void operator()(bvtags::zero_extend_tag const &tag) const {
      boost::any arg = boost::get(boost::vertex_arg, g_, v_);
      unsigned long width = boost::any_cast<unsigned long>(arg);
      outfile_ << "(zero_extend[" << width << "] ";
      BOOST_FOREACH (SMT_Edge e, out_edges(v_, g_)) {
        print_SMT_Expression(outfile_, g_, target(e, g_));
      }
      outfile_ << ')';
    }

    inline void operator()(bvtags::bvbin_tag const &tag) const {
      boost::any arg = boost::get(boost::vertex_arg, g_, v_);
      std::string bin_const = boost::any_cast<std::string>(arg);
      outfile_ << "(bvbin" << bin_const << ")";
    }

    inline void operator()(bvtags::bvhex_tag const &tag) const {
      boost::any arg = boost::get(boost::vertex_arg, g_, v_);
      std::string hex_const = boost::any_cast<std::string>(arg);
      outfile_ << "(bvhex" << hex_const << ")";
    }

    inline void operator()(bvtags::bvsint_tag const &tag) const {
      typedef boost::tuple<long, unsigned long> tuple_type;
      boost::any arg = boost::get(boost::vertex_arg, g_, v_);
      tuple_type const tuple = boost::any_cast<tuple_type>(arg);
      unsigned long const width = tuple.get<1>();
      boost::dynamic_bitset<> bv(width, tuple.get<0>());
      std::string s; to_string(bv, s);
      outfile_ << "(bvbin" << s << ")";
    }

    inline void operator()(bvtags::bvuint_tag const &tag) const {
      typedef boost::tuple<unsigned long, unsigned long> tuple_type;
      boost::any arg = boost::get(boost::vertex_arg, g_, v_);
      tuple_type tuple = boost::any_cast<tuple_type>(arg);
      outfile_ << "(bv" << tuple.get<0>() << "[" << tuple.get<1>() << "])";
    }

    inline void operator()(bvtags::extract_tag const &tag) const {
      typedef boost::tuple<unsigned long, unsigned long> tuple_type;
      boost::any arg = boost::get(boost::vertex_arg, g_, v_);
      tuple_type tuple = boost::any_cast<tuple_type>(arg);
      outfile_ << "(extract[" << tuple.get<0>() << ':' << tuple.get<1>() << "] ";
      BOOST_FOREACH (SMT_Edge e, out_edges(v_, g_)) {
        print_SMT_Expression(outfile_, g_, target(e, g_));
      }
      outfile_ << ")";
    }

    inline void operator()(predtags::nequal_tag const &tag) const {
      outfile_ << "(not (=";
      BOOST_FOREACH (SMT_Edge e, out_edges(v_, g_)) {
        print_SMT_Expression(outfile_, g_, target(e, g_));
      }
      outfile_ << "))";
    }

    inline void operator()(predtags::distinct_tag const &tag) const {
      outfile_ << "(distinct ";
      BOOST_FOREACH (SMT_Edge e, out_edges(v_, g_)) {
        print_SMT_Expression(outfile_, g_, target(e, g_));
      }
      outfile_ << ")";
    }

    inline void operator()(predtags::nand_tag const &tag) const {
      outfile_ << "(not (and";
      BOOST_FOREACH (SMT_Edge e, out_edges(v_, g_)) {
        print_SMT_Expression(outfile_, g_, target(e, g_));
      }
      outfile_ << "))";
    }

    inline void operator()(predtags::nor_tag const &tag) const {
      outfile_ << "(not (or";
      BOOST_FOREACH (SMT_Edge e, out_edges(v_, g_)) {
        print_SMT_Expression(outfile_, g_, target(e, g_));
      }
      outfile_ << "))";
    }

    inline void operator()(predtags::xnor_tag const &tag) const {
      outfile_ << "(not (xor";
      BOOST_FOREACH (SMT_Edge e, out_edges(v_, g_)) {
        print_SMT_Expression(outfile_, g_, target(e, g_));
      }
      outfile_ << "))";
    }

    inline void operator()(predtags::var_tag const &tag) const {
      outfile_ << "p_" << tag.id;
    }

    inline void operator()(bvtags::var_tag const &tag) const {
      outfile_ << "bitv_" << tag.id;
    }

    inline void operator()(arraytags::array_var_tag const &tag) const {
      outfile_ << "array_" << tag.id;
    }

    template <typename T>
    inline typename boost::enable_if<
      typename mpl::has_key< SMT_NameMap, T>::type
    >::type
    operator()(T const &t) const {
      typedef typename mpl::at< SMT_NameMap, T >::type name;

      if (out_degree(v_, g_) != 0) {
        outfile_ << '(' << mpl::c_str<name>::value;
        BOOST_FOREACH (SMT_Edge e, out_edges(v_, g_)) {
          outfile_ << ' ';
          print_SMT_Expression(outfile_, g_, target(e, g_));
        }
        outfile_ << ')';
      } else {
        outfile_ << mpl::c_str<name>::value;
      }
    }

    template <typename T>
    inline typename boost::disable_if<
      typename mpl::has_key< SMT_NameMap, T>::type
    >::type
    operator()(T const &t) const {
      outfile_ << "(MISSING " << t <<")";
    }

  private:
    std::ostream &outfile_;
    SMT_Graph const &g_;
    SMT_Expression const &v_;
  };

  inline void print_SMT_Expression(std::ostream & outfile,
                                   SMT_Graph const &g,
                                   SMT_Expression const &v) {
    outfile << ' ';
    metaSMT::Tag tag = boost::get(boost::vertex_tag, g, v);
    boost::apply_visitor(Vertex_Printer(outfile, g, v), tag);
  }

  struct SMT_Declaration_Printer : public boost::static_visitor<void> {
    SMT_Declaration_Printer(std::ostream &outfile,
                            SMT_Graph const &g,
                            SMT_Expression const &v)
      : outfile_(outfile),
        g_(g), v_(v)
    {}

    inline void operator()(predtags::var_tag const &tag) const {
      outfile_ << " :extrapreds ((" << "p_" << tag.id << "))\n";
    }

    inline void operator()(bvtags::var_tag const &tag) const {
      outfile_ << " :extrafuns ((" << "bitv_" << tag.id
               << " BitVec[" << tag.width << "]))\n";
    }

    inline void operator()(arraytags::array_var_tag const &tag) const {
      outfile_ << " :extrafuns ((" << "array_" << tag.id
               << " Array[" << tag.index_width << ':' << tag.elem_width << "]))\n";
    }

    template <typename T>
    inline void operator()(T const &t) const
    {}

  private:
    std::ostream &outfile_;
    SMT_Graph const &g_;
    SMT_Expression const &v_;
  };

  inline void write_smt(std::ostream & outfile,
                        SMT_Graph const & g,
                        std::vector<SMT_Expression> const &assertions) {
    outfile
      << "(benchmark metaSMT.smt\n"
      << " :source { Generated by metaSMT }\n"
      << " :status unknown\n"
      << " :difficulty unknown\n"
      << " :logic QF_BV\n"
    ;

    BOOST_FOREACH (SMT_Expression v, vertices(g)) {
      metaSMT::Tag tag = boost::get(boost::vertex_tag, g, v);
      boost::apply_visitor(SMT_Declaration_Printer(outfile, g, v), tag);
    }

    BOOST_FOREACH (SMT_Expression v, assertions) {
      outfile << " :assumption ";
      print_SMT_Expression(outfile, g, v);
      outfile << '\n'; // assertion
    }

    // outfile << " :formula true\n";

    outfile << ")\n"; // benchmark
  }
}
