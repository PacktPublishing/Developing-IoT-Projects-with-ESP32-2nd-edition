cmake_minimum_required(VERSION 3.10)

set(FlatBuffers_Library_SRCS
  include/flatbuffers/allocator.h
  include/flatbuffers/array.h
  include/flatbuffers/base.h
  include/flatbuffers/bfbs_generator.h
  include/flatbuffers/buffer.h
  include/flatbuffers/buffer_ref.h
  include/flatbuffers/default_allocator.h
  include/flatbuffers/detached_buffer.h
  include/flatbuffers/flatbuffer_builder.h
  include/flatbuffers/flatbuffers.h
  include/flatbuffers/flexbuffers.h
  include/flatbuffers/hash.h
  include/flatbuffers/idl.h
  include/flatbuffers/minireflect.h
  include/flatbuffers/reflection.h
  include/flatbuffers/reflection_generated.h
  include/flatbuffers/registry.h
  include/flatbuffers/stl_emulation.h
  include/flatbuffers/string.h
  include/flatbuffers/struct.h
  include/flatbuffers/table.h
  include/flatbuffers/util.h
  include/flatbuffers/vector.h
  include/flatbuffers/vector_downward.h
  include/flatbuffers/verifier.h
  src/idl_parser.cpp
  src/idl_gen_text.cpp
  src/reflection.cpp
  src/util.cpp
)

file(GLOB SOURCES ${FlatBuffers_Library_SRCS})

idf_component_register(
    SRCS ${SOURCES}
    INCLUDE_DIRS include
    )
