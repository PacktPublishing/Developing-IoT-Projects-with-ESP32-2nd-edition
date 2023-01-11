# For more information about build system see
# https://docs.espressif.com/projects/esp-idf/en/latest/api-guides/build-system.html
# The following five lines of boilerplate have to be in your project's
# CMakeLists in this exact order for cmake to work correctly
cmake_minimum_required(VERSION 3.5)

set(EXTRA_COMPONENT_DIRS ../common)

if(DEFINED ENV{MQTT_USER})
  add_compile_options(-DMQTT_USER=$ENV{MQTT_USER})
else(DEFINED ENV{MQTT_USER})
  message(FATAL_ERROR "MQTT username is needed")
endif(DEFINED ENV{MQTT_USER})

if(DEFINED ENV{MQTT_PWD})
  add_compile_options(-DMQTT_PWD=$ENV{MQTT_PWD})
else(DEFINED ENV{MQTT_USER})
  message(FATAL_ERROR "MQTT password is needed")
endif(DEFINED ENV{MQTT_PWD})

include($ENV{IDF_PATH}/tools/cmake/project.cmake)
project(mqtt_ex)
