# Include filepaths for source and include.
include( ${MODULE_ROOT_DIR}/otaFilePaths.cmake )
include( ${MODULE_ROOT_DIR}/otaDependenyFilePaths.cmake )

# ====================  Define your project name (edit) ========================
set(project_name "aws_ota")

# ================= Create the library under test here (edit) ==================


set( OTA_C_TMP_BASE "${CMAKE_BINARY_DIR}/ota" )

# Strip static constraints so unit tests may call internal functions
execute_process( COMMAND sed "s/^static //"
                 WORKING_DIRECTORY ${CMAKE_BINARY_DIR}
                 INPUT_FILE "${MODULE_ROOT_DIR}/source/ota.c"
                 OUTPUT_FILE ${OTA_C_TMP_BASE}.c
)

# list the files you would like to test here
list(APPEND real_source_files
    ${OTA_C_TMP_BASE}.c
    "${MODULE_ROOT_DIR}/source/ota_interface.c"
    "${MODULE_ROOT_DIR}/source/ota_base64.c"
    "${MODULE_ROOT_DIR}/source/ota_mqtt.c"
    "${MODULE_ROOT_DIR}/source/ota_http.c"
    "${MODULE_ROOT_DIR}/source/ota_cbor.c"
    "${MODULE_ROOT_DIR}/source/portable/os/ota_os_posix.c"
    ${TINYCBOR_SOURCES}
    ${JSON_SOURCES}
    "utest_helpers.c"
)
# list the directories the module under test includes
list(APPEND real_include_directories
    "."
    ${OTA_INCLUDE_PUBLIC_DIRS}
    ${OTA_INCLUDE_PRIVATE_DIRS}
    ${OTA_INCLUDE_OS_POSIX_DIRS}
    ${JSON_INCLUDE_PUBLIC_DIRS}
    ${TINYCBOR_INCLUDE_DIRS}
)

# =====================  Create UnitTest Code here (edit)  =====================

# list the directories your test needs to include
list(APPEND test_include_directories ".")

# =============================  (end edit)  ===================================

set(real_name "${project_name}_real")

create_real_library(${real_name}
    "${real_source_files}"
    "${real_include_directories}"
    ""
)
# Suppress warnings in dependency folder
set_source_files_properties(
    ${JSON_SOURCES}
    ${TINYCBOR_SOURCES}
    PROPERTIES COMPILE_FLAGS
    "-w"
)
target_include_directories(${real_name}
    SYSTEM PRIVATE
    ${TINYCBOR_INCLUDE_DIRS}
    ${JSON_INCLUDE_PUBLIC_DIRS}
)

list(APPEND utest_link_list
    -lpthread
    lib${real_name}.a
    -lrt
)

list(APPEND utest_dep_list
    ${real_name}
)

create_test(ota_utest
    "ota_utest.c"
    "${utest_link_list}"
    "${utest_dep_list}"
    "${test_include_directories}"
)

create_test(ota_base64_utest
    "ota_base64_utest.c"
    "${utest_link_list}"
    "${utest_dep_list}"
    "${test_include_directories}"
)

create_test(ota_cbor_utest
    "ota_cbor_utest.c"
    "${utest_link_list}"
    "${utest_dep_list}"
    "${test_include_directories}"
)

create_test(ota_os_posix_utest
    "ota_os_posix_utest.c"
    "${utest_link_list}"
    "${utest_dep_list}"
    "${test_include_directories}"
)
# Disable unity memory handling since we need to free memory allocated from library.
target_compile_definitions(ota_cbor_utest PRIVATE UNITY_FIXTURE_NO_EXTRAS)
