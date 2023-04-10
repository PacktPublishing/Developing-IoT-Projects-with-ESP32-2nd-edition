# The following five lines of boilerplate have to be in your project's
# CMakeLists in this exact order for cmake to work correctly
cmake_minimum_required(VERSION 3.5)

if(DEFINED ENV{AWSIOT_PATH})
  set(AWSIOT_PATH $ENV{AWSIOT_PATH})
else()
  set(AWSIOT_PATH ${CMAKE_CURRENT_LIST_DIR}/../common/esp-aws-iot)
endif(DEFINED ENV{AWSIOT_PATH})


if(DEFINED ENV{AWS_ENDPOINT})
    message("AWS IoT endpoint: " $ENV{AWS_ENDPOINT})
    add_compile_options(-DAWS_ENDPOINT=$ENV{AWS_ENDPOINT})
else()
    message(FATAL_ERROR "Define AWS_ENDPOINT")
endif(DEFINED ENV{AWS_ENDPOINT})


set(EXTRA_COMPONENT_DIRS 
						 "${AWSIOT_PATH}/libraries/coreMQTT"
						 "${AWSIOT_PATH}/libraries/common/posix_compat"
                         "../common/wifi"
                         "../common/sensor"
                         "../common/espressif__qrcode"
   )

include($ENV{IDF_PATH}/tools/cmake/project.cmake)
project(aws_ex)

target_add_binary_data(${CMAKE_PROJECT_NAME}.elf "tmp/root_cert_auth.crt" TEXT)
target_add_binary_data(${CMAKE_PROJECT_NAME}.elf "tmp/client.crt" TEXT)
target_add_binary_data(${CMAKE_PROJECT_NAME}.elf "tmp/client.key" TEXT)
