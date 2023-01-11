# For more information about build system see
# https://docs.espressif.com/projects/esp-idf/en/latest/api-guides/build-system.html
# The following five lines of boilerplate have to be in your project's
# CMakeLists in this exact order for cmake to work correctly
cmake_minimum_required(VERSION 3.5)

if(DEFINED ENV{WIFI_SSID})
  add_compile_options(-DWIFI_SSID=$ENV{WIFI_SSID})
else(DEFINED ENV{WIFI_SSID})
  message(FATAL_ERROR "WiFi SSID is needed")
endif(DEFINED ENV{WIFI_SSID})

if(DEFINED ENV{WIFI_PWD})
  add_compile_options(-DWIFI_PWD=$ENV{WIFI_PWD})
else(DEFINED ENV{WIFI_PWD})
  message(FATAL_ERROR "WiFi password is needed")
endif(DEFINED ENV{WIFI_PWD})

include($ENV{IDF_PATH}/tools/cmake/project.cmake)
project(wifi_ex)
