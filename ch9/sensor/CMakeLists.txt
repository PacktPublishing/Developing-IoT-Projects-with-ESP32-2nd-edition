# The following lines of boilerplate have to be in your project's CMakeLists
# in this exact order for cmake to work correctly
cmake_minimum_required(VERSION 3.22)

add_compile_options(-fdiagnostics-color=always)

set(CH7_COMMON ${CMAKE_CURRENT_LIST_DIR}/../../ch7/common)

if(DEFINED ENV{PRJ_COMMON_PATH})
  set(RMAKER_PATH $ENV{PRJ_COMMON_PATH}/esp-rainmaker)
else()
  set(RMAKER_PATH ${CH7_COMMON}/esp-rainmaker)
endif()

set(EXTRA_COMPONENT_DIRS 
	${CMAKE_CURRENT_LIST_DIR}/../common/ch9_common
	${CMAKE_CURRENT_LIST_DIR}/../../components/esp-idf-lib/components 
	${CMAKE_CURRENT_LIST_DIR}/../../components
	${RMAKER_PATH}/components/esp-insights/components 
	${RMAKER_PATH}/components
	${RMAKER_PATH}/examples/common
	)

set(PROJECT_VER "1.0")
include($ENV{IDF_PATH}/tools/cmake/project.cmake)
project(sensor)
