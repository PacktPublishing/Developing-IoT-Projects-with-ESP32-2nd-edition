cmake_minimum_required(VERSION 3.10)
set(FlatBuffers_Library_SRCS
  src/idl_parser.cpp
  src/idl_gen_text.cpp
  src/reflection.cpp
  src/util.cpp
)
file(GLOB SOURCES ${FlatBuffers_Library_SRCS})
idf_component_register(SRCS ${SOURCES} INCLUDE_DIRS include)
