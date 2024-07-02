cmake_minimum_required(VERSION 3.13.1)

set(MODEL_FOLDER ..)
set(EI_SDK_FOLDER ../edge-impulse-sdk)

if(NOT CMAKE_BUILD_EARLY_EXPANSION)
add_definitions(-DEI_CLASSIFIER_TFLITE_ENABLE_ESP_NN=1) # enables ESP-NN optimizations by Espressif
# disabled by default - enable if you use ESP32S3
# add_definitions(-DEI_CLASSIFIER_TFLITE_ENABLE_ESP_NN_S3=1) # enables ESP-NN S3 optimizations by Espressif
endif()

OPTION(DEFINE_DEBUG
    "Build the project using debugging code"
    OFF)
IF(DEFINE_DEBUG)
    MESSAGE("Adding Debug flag...")
    ADD_DEFINITIONS(-DDEBUG)
    SET(CMAKE_BUILD_TYPE Debug)
    MESSAGE("Build type is " ${CMAKE_BUILD_TYPE})
ENDIF(DEFINE_DEBUG)

set(include_dirs
    ${MODEL_FOLDER}
    ${MODEL_FOLDER}/tflite-model
    ${MODEL_FOLDER}/model-parameters
    ${EI_SDK_FOLDER}
    ${EI_SDK_FOLDER}/porting/espressif/ESP-NN/include
    ${EI_SDK_FOLDER}/porting/espressif/ESP-NN/src/common
)

include(${EI_SDK_FOLDER}/cmake/utils.cmake)

RECURSIVE_FIND_FILE_EXCLUDE_DIR(SOURCE_FILES "../edge-impulse-sdk" "CMSIS" "*.cpp")
RECURSIVE_FIND_FILE_EXCLUDE_DIR(MODEL_FILES "../tflite-model" "CMSIS" "*.cpp")
RECURSIVE_FIND_FILE_EXCLUDE_DIR(CC_FILES "../edge-impulse-sdk" "CMSIS" "*.cc")
RECURSIVE_FIND_FILE_EXCLUDE_DIR(S_FILES "../edge-impulse-sdk" "CMSIS" "*.s")
RECURSIVE_FIND_FILE_EXCLUDE_DIR(C_FILES "../edge-impulse-sdk" "CMSIS" "*.c")

list(APPEND SOURCE_FILES ${S_FILES})
list(APPEND SOURCE_FILES ${C_FILES})
list(APPEND SOURCE_FILES ${CC_FILES})
list(APPEND SOURCE_FILES ${MODEL_FILES})

idf_component_register(SRCS "main.cpp" "${SOURCE_FILES}"
                       INCLUDE_DIRS "${include_dirs}")

target_compile_options(${COMPONENT_LIB} PRIVATE -std=gnu++17)

