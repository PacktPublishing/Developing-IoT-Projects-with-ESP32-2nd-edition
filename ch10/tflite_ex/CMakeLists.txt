cmake_minimum_required(VERSION 3.5)
set(EXTRA_COMPONENT_DIRS 
    ../../components/
    ../components/tflite-micro-esp-examples/components/bus
    ../components/tflite-micro-esp-examples/components/esp-nn
    ../components/tflite-micro-esp-examples/components/tflite-lib
    )
include($ENV{IDF_PATH}/tools/cmake/project.cmake)
project(tflite_ex)
