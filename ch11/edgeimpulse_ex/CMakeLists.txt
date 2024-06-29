cmake_minimum_required(VERSION 3.15)

set(EXTRA_COMPONENT_DIRS 
../../ch10/components/esp-skainet-extra-components
../../ch10/components/esp-skainet/components)

# set(CMAKE_CXX_FLAGS "-O11 -std=c++11")

include($ENV{IDF_PATH}/tools/cmake/project.cmake)
project(edgeimpulse_ex)

idf_build_set_property(COMPILE_OPTIONS "-fdiagnostics-color=always" APPEND)
idf_build_set_property(COMPILE_OPTIONS "-Wno-uninitialized" APPEND)
idf_build_set_property(COMPILE_OPTIONS "-Wno-unused-variable" APPEND)
idf_build_set_property(COMPILE_OPTIONS "-Wno-maybe-uninitialized" APPEND)
idf_build_set_property(COMPILE_OPTIONS "-Wno-error=format=" APPEND)
idf_build_set_property(COMPILE_OPTIONS "-Wno-unused-but-set-parameter" APPEND)
idf_build_set_property(COMPILE_OPTIONS "-Wno-error=nonnull-compare" APPEND)
idf_build_set_property(COMPILE_OPTIONS "-Wno-error=stringop-truncation" APPEND)
idf_build_set_property(COMPILE_OPTIONS "-DEI_PORTING_ESPRESSIF=1" APPEND)
