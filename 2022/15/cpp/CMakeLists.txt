cmake_minimum_required(VERSION 3.30)

set(CMAKE_EXPERIMENTAL_CXX_IMPORT_STD "0e5b6991-d74f-4b3d-a41c-cf096e0b2508")
set(CMAKE_BUILD_TYPE Release)
set(CMAKE_CXX_MODULE_STD 1)
set(CMAKE_CXX_COMPILER clang++)
set(CMAKE_CXX_FLAGS -stdlib=libc++)
set(CMAKE_CXX_STANDARD 23)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)
set(CTRE_MODULE ON)
set(CTRE_CXX_STANDARD ${CMAKE_CXX_STANDARD})

project(solution LANGUAGES CXX)

include(FetchContent)

FetchContent_Declare(
    ctre
    GIT_REPOSITORY https://github.com/hanickadot/compile-time-regular-expressions
    GIT_TAG v3.9.0
)
FetchContent_MakeAvailable(ctre)

add_library(flags)
target_compile_options(
    flags
    PUBLIC
        -Wall
        -Wextra
        -pedantic
        -Wno-c99-extensions
        -Wconversion
        -Wsign-conversion
        -fcolor-diagnostics
)

add_library(parse_input STATIC)
target_sources(parse_input
    PUBLIC
    FILE_SET cxx_modules TYPE CXX_MODULES FILES
    parse_input.cxx
)
target_link_libraries(parse_input PRIVATE flags ctre)

add_executable(solution solution.cxx)
target_link_libraries(solution PRIVATE flags parse_input)
