# The following lines of boilerplate have to be in your project's CMakeLists
# in this exact order for cmake to work correctly
cmake_minimum_required(VERSION 3.5)

if(DEFINED ENV{INSIGHTS_PATH})
  set(INSIGHTS_PATH $ENV{INSIGHTS_PATH})
else()
  set(INSIGHTS_PATH ${CMAKE_CURRENT_LIST_DIR}/../..)
endif(DEFINED ENV{INSIGHTS_PATH})

# Add RainMaker components
set(EXTRA_COMPONENT_DIRS ${INSIGHTS_PATH}/components ${INSIGHTS_PATH}/examples/common)

set(PROJECT_VER "1.0")
include($ENV{IDF_PATH}/tools/cmake/project.cmake)
project(minimal_diagnostics)
