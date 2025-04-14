cmake_minimum_required(VERSION 3.20)

project(XD VERSION 0.1.0)

set(XD_LLVM_INSTALL_PREFIX "/usr/lib/llvm-20" CACHE STRING "LLVM 20.1.0 install directory")

set(CMAKE_CXX_STANDARD 23)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)
set(CMAKE_ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib)
set(CMAKE_LIBRARY_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib)
set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin)
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

# Force the build to use the LLVM libc++ that was built
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -stdlib=libc++ -I${XD_LLVM_INSTALL_PREFIX}/include/c++/v1")
set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -stdlib=libc++ -L${XD_LLVM_INSTALL_PREFIX}/lib -Wl,-rpath,${XD_LLVM_INSTALL_PREFIX}/lib")
set(CMAKE_SHARED_LINKER_FLAGS "${CMAKE_SHARED_LINKER_FLAGS} -stdlib=libc++ -L${XD_LLVM_INSTALL_PREFIX}/lib -Wl,-rpath,${XD_LLVM_INSTALL_PREFIX}/lib")
set(CMAKE_MODULE_LINKER_FLAGS "${CMAKE_MODULE_LINKER_FLAGS} -stdlib=libc++ -L${XD_LLVM_INSTALL_PREFIX}/lib -Wl,-rpath,${XD_LLVM_INSTALL_PREFIX}/lib")

cmake_policy(SET CMP0135 NEW)

find_package(LLVM 20.1.0 REQUIRED CONFIG PATHS "${XD_LLVM_INSTALL_PREFIX}/")
message(STATUS "Found LLVM ${LLVM_PACKAGE_VERSION} in directory ${LLVM_DIR}")

include(FetchContent)
fetchcontent_declare(googletest GIT_REPOSITORY https://github.com/google/googletest.git GIT_TAG v1.16.0)
fetchcontent_makeavailable(googletest)
include(GoogleTest)

set(EIGHT_INCLUDE_DIRS ${CMAKE_SOURCE_DIR}/compiler/include ${CMAKE_BINARY_DIR}/compiler/include)

macro(add_xd_executable name)
    cmake_parse_arguments(ARG "" "" "SOURCES;LIBS" ${ARGN})
    add_executable(${name} ${ARG_SOURCES})
    target_link_libraries(${name} PRIVATE ${ARG_LIBS})
    target_include_directories(${name} PRIVATE ${EIGHT_INCLUDE_DIRS})
    target_include_directories(${name} PRIVATE ${LLVM_INCLUDE_DIRS})
    target_compile_features(${name} PRIVATE cxx_std_23)
    target_compile_options(${name} PRIVATE -fno-rtti -std=c++23)
    install(TARGETS ${name} DESTINATION ${CMAKE_BINARY_DIR}/bin)
endmacro()

macro(add_xd_tablegen name)
    cmake_parse_arguments(ARG "" "" "FLAGS" ${ARGN})
    add_custom_command(OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/${name}.inc
            COMMAND xd-tablegen ${name} ${ARG_FLAGS} -o ${CMAKE_CURRENT_BINARY_DIR}/${name}.inc
            COMMENT "Building XD TableGen file ${name}"
            DEPENDS ${CMAKE_CURRENT_SOURCE_DIR}/${name}
            WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR})
    add_custom_target(${name} DEPENDS ${CMAKE_CURRENT_BINARY_DIR}/${name}.inc)
    add_dependencies(${name} XDTableGen xd-tablegen)
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
    target_compile_features(${name} PRIVATE cxx_std_23)
    target_compile_options(${name} PRIVATE -fno-rtti -std=c++23)
    install(TARGETS ${name} DESTINATION lib)
endmacro()

enable_testing()

add_subdirectory(compiler)
