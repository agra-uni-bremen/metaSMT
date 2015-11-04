#!/bin/bash
SRC_DIR=$( cd $(dirname $0) && pwd)

BUILD_DIR=$PWD/build

BOOST=boost-1_55_0

REQUIRES="
  $BOOST
"

FREE="
  cryptominisat-git
  cvc4-1.4
  picosat-936
  boolector-1.5.118
  aiger-20071012
  cudd-2.4.2
  minisat-git
  stp-git
  Z3-git
"

NONFREE="
  SWORD-1.1
  lingeling-ayv-86bf266-140429
"

TRAVIS="
  boolector-1.5.118
  cudd-2.4.2
  minisat-git
"

CMAKE=cmake
BUILD_CMAKE="no"
CMAKE_PACKAGE=cmake-3.2.2

CMAKE_ARGS=""
CMAKE_GENERATOR=""

num_threads="1"


usage() {
  cat << EOF
$0 sets up a metaSMT build directory.
usage: $0 [--free] [--non-free] build
  --help          show this help
  --free          include free backends (Aiger, Boolector, CUDD, PicoSat, ...)
  --non-free      include non-free backends (SWORD, Lingeling)
  --travis        include selected free backends for testing with Travis CI
  --clean         delete build directory before creating a new one
  --deps <dir>    build dependencies in this directory
   -d <dir>       can be shared in different projects
  --install <dir> configure to install to this directory
   -i <dir>
  --mode <type>   the CMake build type to configure, types are
   -m <type>      RELEASE, MINSIZEREL, RELWITHDEBINFO, DEBUG
   -Dvar=val      pass options to CMake
   -G <generator> pass generator to CMake
  --cmake=/p/t/c  use this version of CMake
  --cmake         build a custom CMake version
  --build <pkg>   build this dependency package, must exist in depdencies
  -b <pkg>
  -j N            The number of make jobs
  <build>         the directory to setup the build environment in
EOF
  exit 1
}

if ! [[ "$1" ]]; then
  usage
fi



while [[ "$@" ]]; do
  case $1 in
    --help|-h)    usage;;
    --free)       REQUIRES="$REQUIRES $FREE" ;;
    --non-free)   REQUIRES="$REQUIRES $NONFREE" ;;
    --travis)     REQUIRES="$REQUIRES $TRAVIS" ;;
    --deps|-d)    DEPS="$2"; shift;;
    --install|-i) INSTALL="$2"; shift;;
    --mode|-m)    CMAKE_ARGS="$CMAKE_ARGS -DCMAKE_BUILD_TYPE=$2"; shift;;
     -D*)         CMAKE_ARGS="$CMAKE_ARGS '$1'";;
     -G)          CMAKE_GENERATOR="$2" && shift;;
    --clean|-c)   CLEAN="rm -rf";;
    --cmake=*)    CMAKE="${1#--cmake=}";;
    --cmake)      BUILD_CMAKE="yes";;
    --build|-b)   REQUIRES="$REQUIRES $2"; shift;;
    -j)
        num_threads="$2";
        shift;;
    -j*)
        num_threads="${1/-j}";;

             *)   ## assume build dir
                  BUILD_DIR="$1" ;;
  esac
  shift;
done


if [[ "$CLEAN" ]]; then
  rm -rf $BUILD_DIR
fi

mk_and_abs_dir() {
  mkdir -p $1 &&
  cd $1 &>/dev/null &&
  pwd
}
BUILD_DIR=$(mk_and_abs_dir $BUILD_DIR) &&
INSTALL=$(mk_and_abs_dir ${INSTALL:-$BUILD_DIR/root}) &&
DEPS=$(mk_and_abs_dir ${DEPS:-$BUILD_DIR}) &&


if ! cd dependencies; then 
    echo 'Missing "dependencies" directory. Please refer to the README.md for more details.'
    exit 2
fi

if [ "$BUILD_CMAKE" = "yes" ]; then
  ./build -j $num_threads "$DEPS" $CMAKE_PACKAGE &&
  CMAKE=$DEPS/$CMAKE_PACKAGE/bin/cmake
  export PATH="$DEPS/$CMAKE_PACKAGE/bin:$PATH"
fi

./build -j $num_threads "$DEPS" $REQUIRES || {
  echo "building dependencies $REQUIRES failed."
  exit 3
}
cd $BUILD_DIR && 

PREFIX_PATH=$(echo $REQUIRES| sed "s@[ ^] *@;$DEPS/@g")

eval_echo() {
  local RESULT=true
  $@ || RESULT=false
  echo "$@"

  $RESULT || exit 1
}

EXIT=true;

cd $BUILD_DIR
eval_echo $CMAKE \
  ${CMAKE_GENERATOR:+-G} "$CMAKE_GENERATOR" \
  -DCMAKE_INSTALL_PREFIX="$INSTALL" \
  -DCMAKE_PREFIX_PATH="$PREFIX_PATH" \
  $CMAKE_ARGS \
  -DBOOST_ROOT="$DEPS/$BOOST" \
  $SRC_DIR


echo "finished bootstrap, you can now call make in $BUILD_DIR"

