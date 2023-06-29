# For more information about build system see
# https://docs.espressif.com/projects/esp-idf/en/latest/api-guides/build-system.html
# The following five lines of boilerplate have to be in your project's
# CMakeLists in this exact order for cmake to work correctly
cmake_minimum_required(VERSION 3.15)
set(EXTRA_COMPONENT_DIRS 
../components/esp-skainet/components/esp_codec_dev
../components/esp-skainet/components/esp-dsp
../components/esp-skainet/components/esp-sr
../components/esp-skainet/components/hardware_driver
../components/esp-skainet/components/led_strip
../components/esp-skainet/components/perf_tester
../components/esp-skainet/components/player
../components/esp-skainet/components/sr_ringbuf)
include($ENV{IDF_PATH}/tools/cmake/project.cmake)
project(speech_ex)
