cmake_minimum_required(VERSION 3.20)

project(Eight VERSION 0.1.0)

find_package(LLVM 18.1.3 REQUIRED CONFIG)
message(STATUS "Found LLVM ${LLVM_PACKAGE_VERSION} in directory ${LLVM_DIR}")

set(CMAKE_CXX_STANDARD 20)
set(CMAKE_ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib)
set(CMAKE_LIBRARY_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib)
set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin)
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

set(EIGHT_INCLUDE_DIRS ${CMAKE_SOURCE_DIR}/compiler/include)

macro(add_eight_executable name)
    cmake_parse_arguments(ARG "" "" "SOURCES;LIBS" ${ARGN})
    add_executable(${name} ${ARG_SOURCES})
    target_link_libraries(${name} PUBLIC ${ARG_LIBS})
    target_include_directories(${name} PUBLIC ${EIGHT_INCLUDE_DIRS})
    target_include_directories(${name} PUBLIC ${LLVM_INCLUDE_DIRS})
    # TableGen files are generated in the build directory
    target_include_directories(${name} PUBLIC ${CMAKE_BINARY_DIR}/include)
    target_compile_features(${name} PRIVATE cxx_std_20)
    target_compile_options(${name} PRIVATE -fno-rtti -std=c++20)
    install(TARGETS ${name} DESTINATION ${CMAKE_BINARY_DIR}/bin)
endmacro()

macro(add_eight_library name)
    cmake_parse_arguments(ARG "" "" "SOURCES;LIBS" ${ARGN})
    add_library(${name} ${ARG_SOURCES})
    target_link_libraries(${name} PUBLIC ${ARG_LIBS})
    target_include_directories(${name} PUBLIC ${EIGHT_INCLUDE_DIRS})
    target_include_directories(${name} PUBLIC ${LLVM_INCLUDE_DIRS})
    # TableGen files are generated in the build directory
    target_include_directories(${name} PUBLIC ${CMAKE_BINARY_DIR}/include)
    target_compile_features(${name} PRIVATE cxx_std_20)
    target_compile_options(${name} PRIVATE -fno-rtti -std=c++20)
    install(TARGETS ${name} DESTINATION lib)
endmacro()

enable_testing()

add_subdirectory(compiler)
