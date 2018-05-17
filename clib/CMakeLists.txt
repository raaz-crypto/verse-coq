cmake_minimum_required(VERSION 3.0.0)
project(verse)

set(CMAKE_CXX_FLAGS "-Wall -Wextra")

include_directories(.)

add_library(verse SHARED verse.c)
