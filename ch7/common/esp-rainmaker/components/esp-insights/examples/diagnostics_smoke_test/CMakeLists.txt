# The following lines of boilerplate have to be in your project's CMakeLists
# in this exact order for cmake to work correctly
cmake_minimum_required(VERSION 3.5)


# This example uses an extra component from IDF for common functions such as Wi-Fi and Ethernet connection.
set(EXTRA_COMPONENT_DIRS $ENV{IDF_PATH}/examples/common_components/protocol_examples_common)

# Add Insights components. Not required if espressif/esp_insights is included via IDF component manager */
if(DEFINED ENV{INSIGHTS_PATH})
  set(INSIGHTS_PATH $ENV{INSIGHTS_PATH})
else()
  set(INSIGHTS_PATH ${CMAKE_CURRENT_LIST_DIR}/../..)
endif(DEFINED ENV{INSIGHTS_PATH})
list(APPEND EXTRA_COMPONENT_DIRS ${INSIGHTS_PATH}/components)

set(PROJECT_VER "1.0")
include($ENV{IDF_PATH}/tools/cmake/project.cmake)
project(diagnostics_smoke_test)
