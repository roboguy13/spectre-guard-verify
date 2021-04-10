cmake_minimum_required(VERSION 3.1)
project(SGVerifier)

# support C++14 features used by LLVM 10.0.0
set(CMAKE_CXX_STANDARD 14)
set(CMAKE_CXX_FLAGS "-DLLVM_DISABLE_ABI_BREAKING_CHECKS_ENFORCING=1 -fno-rtti")
set(CMAKE_SHARED_LINKER_FLAGS "-undefined dynamic_lookup")

find_package(LLVM REQUIRED CONFIG)
# list(APPEND CMAKE_MODULE_PATH "${LLVM_CMAKE_DIR}")
# include(AddLLVM)
add_definitions(${LLVM_DEFINITIONS})
include_directories(${LLVM_INCLUDE_DIRS})
link_directories(${LLVM_LIBRARY_DIRS})

add_subdirectory(src)
