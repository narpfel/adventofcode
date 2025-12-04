cmake_minimum_required(VERSION 4.2)

set(CMAKE_EXPERIMENTAL_CXX_IMPORT_STD "d0edc3af-4c50-42ea-a356-e2862fe7a444")
set(CMAKE_BUILD_TYPE Release)
set(CMAKE_CXX_MODULE_STD 1)
set(CMAKE_CXX_COMPILER g++)
set(CMAKE_CXX_STANDARD 23)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

project(solution LANGUAGES CXX)

add_executable(solution main.cxx)
target_compile_options(
    solution
    PRIVATE
        -Wall
        -Wextra
        -pedantic
        -Wconversion
        -Wsign-conversion
        -fdiagnostics-color=always
)
