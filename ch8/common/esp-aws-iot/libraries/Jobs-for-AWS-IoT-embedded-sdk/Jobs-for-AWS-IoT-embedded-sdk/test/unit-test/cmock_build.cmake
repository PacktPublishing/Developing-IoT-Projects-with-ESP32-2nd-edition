# Macro utility to clone the CMock submodule.
macro( clone_cmock )
        find_package( Git REQUIRED )
        message( "Cloning submodule CMock." )
        execute_process( COMMAND rm -rf ${CMOCK_DIR}
                         COMMAND ${GIT_EXECUTABLE} submodule update --init --recursive ${CMOCK_DIR}
                        WORKING_DIRECTORY ${PROJECT_SOURCE_DIR}
                        RESULT_VARIABLE CMOCK_CLONE_RESULT )

        if( NOT ${CMOCK_CLONE_RESULT} STREQUAL "0" )
                message( FATAL_ERROR "Failed to clone CMock submodule." )
        endif()
endmacro()

# Macro utility to add library targets for Unity and CMock to build configuration.
macro( add_cmock_targets )
        # Build Configuration for CMock and Unity libraries.
        list( APPEND CMOCK_INCLUDE_DIRS
                "${CMOCK_DIR}/vendor/unity/src/"
                "${CMOCK_DIR}/vendor/unity/extras/fixture/src"
                "${CMOCK_DIR}/vendor/unity/extras/memory/src"
                "${CMOCK_DIR}/src"
        )

        add_library(unity STATIC
                "${CMOCK_DIR}/vendor/unity/src/unity.c"
                "${CMOCK_DIR}/vendor/unity/extras/fixture/src/unity_fixture.c"
                "${CMOCK_DIR}/vendor/unity/extras/memory/src/unity_memory.c"
                )

        set_target_properties(unity PROPERTIES
                ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib
                POSITION_INDEPENDENT_CODE ON
                )

        target_include_directories(unity PUBLIC
                ${CMOCK_INCLUDE_DIRS}
                )

        target_link_libraries(unity)
endmacro()
