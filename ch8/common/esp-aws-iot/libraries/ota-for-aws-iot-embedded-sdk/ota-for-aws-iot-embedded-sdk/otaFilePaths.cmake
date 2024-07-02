# This file is to add source files and include directories
# into variables so that it can be reused from different repositories
# in their Cmake based build system by including this file.
#
# Files specific to the repository such as test runner, platform tests
# are not added to the variables.

# OTA library source files, including 3rdparties.
set( OTA_SOURCES
    "${CMAKE_CURRENT_LIST_DIR}/source/include/ota.h"
    "${CMAKE_CURRENT_LIST_DIR}/source/include/ota_os_interface.h"
    "${CMAKE_CURRENT_LIST_DIR}/source/include/ota_platform_interface.h"
    "${CMAKE_CURRENT_LIST_DIR}/source/include/ota_private.h"
    "${CMAKE_CURRENT_LIST_DIR}/source/include/ota_interface_private.h"
    "${CMAKE_CURRENT_LIST_DIR}/source/include/ota_base64_private.h"
    "${CMAKE_CURRENT_LIST_DIR}/source/ota.c"
    "${CMAKE_CURRENT_LIST_DIR}/source/ota_interface.c"
    "${CMAKE_CURRENT_LIST_DIR}/source/ota_base64.c"
)

# OTA library public include directories.
set( OTA_INCLUDE_PUBLIC_DIRS
    "${CMAKE_CURRENT_LIST_DIR}/source/include"
    "${CMAKE_CURRENT_LIST_DIR}/source/portable"
)

# OTA library private include directories.
set( OTA_INCLUDE_PRIVATE_DIRS
    "${CMAKE_CURRENT_LIST_DIR}/source"
)

# OTA library POSIX OS porting source files.
# Note: user needs to call find_library(LIB_RT rt REQUIRED) and link with
# ${LIB_RT} because librt is required to use OTA OS POSIX port.
set( OTA_OS_POSIX_SOURCES
    "${CMAKE_CURRENT_LIST_DIR}/source/portable/os/ota_os_posix.c"
)

# OTA library POSIX OS porting source files.
set( OTA_INCLUDE_OS_POSIX_DIRS
    "${CMAKE_CURRENT_LIST_DIR}/source/portable/os"
)

# OTA library FreeRTOS OS porting source files.
set( OTA_OS_FREERTOS_SOURCES
    "${CMAKE_CURRENT_LIST_DIR}/source/portable/os/ota_os_freertos.c"
)

# OTA library FreeRTOS OS porting source files.
set( OTA_INCLUDE_OS_FREERTOS_DIRS
    "${CMAKE_CURRENT_LIST_DIR}/source/portable/os"
)

# OTA library MQTT backend source files.
set( OTA_MQTT_SOURCES
    "${CMAKE_CURRENT_LIST_DIR}/source/ota_mqtt.c"
    "${CMAKE_CURRENT_LIST_DIR}/source/ota_cbor.c"
    "${CMAKE_CURRENT_LIST_DIR}/source/include/ota_mqtt_private.h"
    "${CMAKE_CURRENT_LIST_DIR}/source/include/ota_cbor_private.h"
)

# OTA library HTTP backend source files.
set( OTA_HTTP_SOURCES
    "${CMAKE_CURRENT_LIST_DIR}/source/ota_http.c"
    "${CMAKE_CURRENT_LIST_DIR}/source/include/ota_http_private.h"
)
