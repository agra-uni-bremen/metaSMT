#include "SortNetSynth.hpp"

#include <boost/format.hpp>

#include <iostream>

template<typename SynthContext, typename VerifyContext>
class Main
{
  public:
    Main(int argc, const char** argv)
      : argc(argc)
      , argv(argv)
    {
    }

    int run()
    {
      if (argc < 3) {
        return usage();
      }

      unsigned min_depth = atoi ( argv[1] );

      std::vector<std::string> inits;
      for (int i = 2; i < argc; ++i)
      {
        inits.push_back(argv[i]);
      }

      SortNetSynth<SynthContext, VerifyContext> synth(min_depth, inits);

      synth();

      std::cout
        << boost::format("Synthesis Time:    %6.2fs\n") % synth.time_synth
        << boost::format("Verification Time: %6.2fs\n") % synth.time_verify;

      return 0;
    }

  private:
    int usage()
    {
      std::cout
        << "usage: "<< argv[0]
        << "<minimual depth of the sortnet> <input> [...]"
        << std::endl;
      return 1;
    }

  private:
    int argc;
    const char** argv;
};

