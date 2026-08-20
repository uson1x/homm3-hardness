cmake_minimum_required(VERSION 3.21)
project(vcmi_engine_check CXX)

# Out-of-source harness that links the *prebuilt* libvcmi.dylib and drives the real
# VCMI combat classes (DamageCalculator, CUnitState, CHealth, CBattleInfoCallback).
# The VCMI checkout is used read-only: headers and the googletest/gmock sources that
# ship with it are compiled from their original location, nothing is written back.

set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

set(VCMI_SRC "$ENV{VCMI_CHECKOUT}" CACHE PATH "VCMI source tree (defaults to $VCMI_CHECKOUT)")

# Object files of the `vcmiMain` OBJECT library, built out-of-source from VCMI_SRC by
# build-libvcmi.sh. We link these directly instead of the shipped libvcmi.dylib for two
# reasons. First, the checked-in build under VCMI_SRC/builds is four months older than the
# source tree and its enum layout no longer matches the headers (see REPORT.md). Second,
# the facade target that produces libvcmi.dylib only links the AI backends when the game
# client is enabled, so a library-only build cannot link it at all; AIFactory.cpp.o is the
# single object that needs them and nothing in this harness calls it.
set(VCMI_OBJ_DIR "" CACHE PATH "vcmiMain object directory (out-of-source lib build of VCMI_SRC; see build.sh)")

set(VCMI_LUA_OBJ_DIR "${VCMI_OBJ_DIR}/../../../luascript/CMakeFiles/vcmiLua.dir"
    CACHE PATH "vcmiLua object directory")

file(GLOB_RECURSE VCMI_OBJECTS "${VCMI_OBJ_DIR}/*.o" "${VCMI_LUA_OBJ_DIR}/*.o")
list(FILTER VCMI_OBJECTS EXCLUDE REGEX "AIFactory\\.cpp\\.o$")
list(LENGTH VCMI_OBJECTS VCMI_OBJECT_COUNT)
if(VCMI_OBJECT_COUNT LESS 100)
    message(FATAL_ERROR "Only ${VCMI_OBJECT_COUNT} vcmiMain objects found in ${VCMI_OBJ_DIR}; run build-libvcmi.sh first")
endif()
message(STATUS "Linking ${VCMI_OBJECT_COUNT} vcmiMain object files")

set(GTEST_SRC "${VCMI_SRC}/test/googletest/googletest")
set(GMOCK_SRC "${VCMI_SRC}/test/googletest/googlemock")

find_package(Boost REQUIRED COMPONENTS filesystem program_options date_time locale)

add_library(gmock_all STATIC
    "${GTEST_SRC}/src/gtest-all.cc"
    "${GMOCK_SRC}/src/gmock-all.cc"
)
target_include_directories(gmock_all PUBLIC
    "${GTEST_SRC}" "${GTEST_SRC}/include"
    "${GMOCK_SRC}" "${GMOCK_SRC}/include"
)
target_compile_options(gmock_all PRIVATE -Wno-everything)

add_executable(enginecheck
    harness.cpp
    "${VCMI_SRC}/test/mock/mock_BonusBearer.cpp"
    "${VCMI_SRC}/test/mock/BattleFake.cpp"
    stubs.cpp
    ${VCMI_OBJECTS}
)
target_compile_definitions(enginecheck PRIVATE VCMI_DLL=1)

# test/ must come before the VCMI root: both provide a "StdInc.h" and we need the test
# one, which pulls in gtest/gmock before the mock headers use the MOCK_METHOD macros.
target_include_directories(enginecheck PRIVATE
    "${VCMI_SRC}/test"
    "${VCMI_SRC}"
    "${VCMI_SRC}/include"
    "${VCMI_SRC}/lib"
    "${Boost_INCLUDE_DIRS}"
)

find_library(MINIZIP_LIB NAMES minizip-ng minizip PATHS /opt/homebrew/lib REQUIRED)
find_library(TBB_LIB tbb PATHS /opt/homebrew/lib REQUIRED)
find_library(LZMA_LIB lzma REQUIRED)
find_library(ZSTD_LIB zstd PATHS /opt/homebrew/lib REQUIRED)
find_library(LUAJIT_LIB NAMES luajit-5.1 luajit PATHS /opt/homebrew/lib REQUIRED)

target_link_libraries(enginecheck PRIVATE
    gmock_all
    Boost::filesystem Boost::program_options Boost::date_time Boost::locale
    ${MINIZIP_LIB} ${TBB_LIB} ${LZMA_LIB} ${ZSTD_LIB}
    ${LUAJIT_LIB}
    z bz2 iconv
    "-framework CoreFoundation" "-framework Security"
)
