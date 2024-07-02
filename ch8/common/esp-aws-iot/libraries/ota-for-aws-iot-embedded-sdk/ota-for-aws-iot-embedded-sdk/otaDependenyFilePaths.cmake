# This file is to add source files and include directories
# into variables so that it can be reused from different repositories
# in their Cmake based build system by including this file.
#
# Files specific to the repository such as test runner, platform tests
# are not added to the variables.

# 3rdparty source files.
include( ${CMAKE_CURRENT_LIST_DIR}/source/dependency/coreJSON/jsonFilePaths.cmake )

set( TINYCBOR_SOURCES
    "${CMAKE_CURRENT_LIST_DIR}/source/dependency/3rdparty/tinycbor/src/cborpretty.c"
    "${CMAKE_CURRENT_LIST_DIR}/source/dependency/3rdparty/tinycbor/src/cborpretty_stdio.c"
    "${CMAKE_CURRENT_LIST_DIR}/source/dependency/3rdparty/tinycbor/src/cborencoder.c"
    "${CMAKE_CURRENT_LIST_DIR}/source/dependency/3rdparty/tinycbor/src/cborencoder_close_container_checked.c"
    "${CMAKE_CURRENT_LIST_DIR}/source/dependency/3rdparty/tinycbor/src/cborerrorstrings.c"
    "${CMAKE_CURRENT_LIST_DIR}/source/dependency/3rdparty/tinycbor/src/cborparser.c"
    "${CMAKE_CURRENT_LIST_DIR}/source/dependency/3rdparty/tinycbor/src/cborparser_dup_string.c"
)
set(TINYCBOR_INCLUDE_DIRS
    "${CMAKE_CURRENT_LIST_DIR}/source/dependency/3rdparty/tinycbor/src"
)
# Use C99 for tinycbor as it is incompatible with C90
if(CMAKE_C_STANDARD LESS 99)
    set_source_files_properties(
        ${TINYCBOR_SOURCES}
        PROPERTIES
        COMPILE_FLAGS "-std=gnu99"
    )
endif()