cmake_minimum_required(VERSION 3.20)

project(XD VERSION 0.1.0)

set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib)
set(CMAKE_LIBRARY_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib)
set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin)
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

cmake_policy(SET CMP0135 NEW)

find_package(LLVM 18.1.3 REQUIRED CONFIG)
message(STATUS "Found LLVM ${LLVM_PACKAGE_VERSION} in directory ${LLVM_DIR}")

include(FetchContent)

# Ubuntu-sourced LLVM 18 is built with libstdc++, but GoogleTest will try to include <cxxabi.h> because we have LLVM
# include directories in the include path.
add_definitions(-DGTEST_HAS_CXXABI_H_=0)
fetchcontent_declare(googletest GIT_REPOSITORY https://github.com/google/googletest.git GIT_TAG v1.16.0)
fetchcontent_makeavailable(googletest)
include(GoogleTest)

set(EIGHT_INCLUDE_DIRS ${CMAKE_SOURCE_DIR}/compiler/include)

macro(add_xd_executable name)
    cmake_parse_arguments(ARG "" "" "SOURCES;LIBS" ${ARGN})
    add_executable(${name} ${ARG_SOURCES})
    target_link_libraries(${name} PRIVATE ${ARG_LIBS})
    target_include_directories(${name} PRIVATE ${EIGHT_INCLUDE_DIRS})
    target_include_directories(${name} PRIVATE ${LLVM_INCLUDE_DIRS})
    # TableGen files are generated in the build directory
    target_include_directories(${name} PRIVATE ${CMAKE_BINARY_DIR}/include)
    target_compile_features(${name} PRIVATE cxx_std_20)
    target_compile_options(${name} PRIVATE -fno-rtti -std=c++20)
    install(TARGETS ${name} DESTINATION ${CMAKE_BINARY_DIR}/bin)
endmacro()

macro(add_xd_test name)
    cmake_parse_arguments(ARG "" "" "SOURCES;LIBS" ${ARGN})
    add_xd_executable(${name} SOURCES ${ARG_SOURCES} LIBS ${ARG_LIBS})
    target_link_libraries(${name} PRIVATE GTest::gtest_main)
    gtest_discover_tests(${name})
endmacro()

macro(add_xd_library name)
    cmake_parse_arguments(ARG "" "" "SOURCES;LIBS" ${ARGN})
    add_library(${name} ${ARG_SOURCES})
    target_link_libraries(${name} PRIVATE ${ARG_LIBS})
    target_include_directories(${name} PRIVATE ${EIGHT_INCLUDE_DIRS})
    target_include_directories(${name} PRIVATE ${LLVM_INCLUDE_DIRS})
    # TableGen files are generated in the build directory
    target_include_directories(${name} PRIVATE ${CMAKE_BINARY_DIR}/include)
    target_compile_features(${name} PRIVATE cxx_std_20)
    target_compile_options(${name} PRIVATE -fno-rtti -std=c++20)
    install(TARGETS ${name} DESTINATION lib)
endmacro()

enable_testing()

add_subdirectory(compiler)
