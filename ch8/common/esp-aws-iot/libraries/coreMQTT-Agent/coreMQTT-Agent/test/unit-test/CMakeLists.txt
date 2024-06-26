# ====================  Define your project name (edit) ========================
set(project_name "mqtt_agent")

# =====================  Create your mock here  (edit)  ========================

# list the files to mock here
list(APPEND mock_list
            "${MODULE_ROOT_DIR}/source/dependency/coreMQTT/source/include/core_mqtt.h"
            "${MODULE_ROOT_DIR}/source/dependency/coreMQTT/source/include/core_mqtt_state.h"
            "${MODULE_ROOT_DIR}/source/include/core_mqtt_agent_command_functions.h"
        )

list(APPEND mock_list_command_functions
            "${MODULE_ROOT_DIR}/source/dependency/coreMQTT/source/include/core_mqtt.h"
            "${MODULE_ROOT_DIR}/source/dependency/coreMQTT/source/include/core_mqtt_state.h"
            "${MODULE_ROOT_DIR}/source/include/core_mqtt_agent.h"
        )

# list the directories your mocks need
list(APPEND mock_include_list
            .
            ${CMAKE_CURRENT_LIST_DIR}/logging
            ${CMAKE_CURRENT_LIST_DIR}/config
            ${MQTT_AGENT_INCLUDE_PUBLIC_DIRS}
            ${MQTT_INCLUDE_PUBLIC_DIRS}
        )

#list the definitions of your mocks to control what to be included
list(APPEND mock_define_list
            ""
       )

# ================= Create the library under test here (edit) ==================

# list the files you would like to test here
list(APPEND real_source_files
            ${MQTT_AGENT_SOURCES}
        )
# list the directories the module under test includes
list(APPEND real_include_directories
            .
            ${CMAKE_CURRENT_LIST_DIR}/logging
            ${CMAKE_CURRENT_LIST_DIR}/config
            ${MQTT_AGENT_INCLUDE_PUBLIC_DIRS}
            ${MQTT_INCLUDE_PUBLIC_DIRS}
        )

# =====================  Create UnitTest Code here (edit)  =====================

# list the directories your test needs to include
list(APPEND test_include_directories
            .
            ${MQTT_AGENT_INCLUDE_PUBLIC_DIRS}
        )

# =============================  (end edit)  ===================================

set(mock_name "${project_name}_mock")
set(real_name "${project_name}_real")

create_mock_list(${mock_name}
                "${mock_list}"
                "${MODULE_ROOT_DIR}/tools/cmock/project.yml"
                "${mock_include_list}"
                "${mock_define_list}"
        )

create_real_library(${real_name}
                    "${real_source_files}"
                    "${real_include_directories}"
                    "${mock_name}"
        )

list(APPEND utest_link_list
            -l${mock_name}
            lib${real_name}.a
        )

list(APPEND utest_dep_list
            ${real_name}
        )


# mqtt_agent_utest
set(utest_name "${project_name}_utest")
set(utest_source "${project_name}_utest.c")
create_test(${utest_name}
            ${utest_source}
            "${utest_link_list}"
            "${utest_dep_list}"
            "${test_include_directories}"
        )

# mqtt_agent_command_functions_utest
set(mock_name "${project_name}_command_functions_mock")
set(real_name "${project_name}_command_functions_real")
create_mock_list(${mock_name}
                "${mock_list_command_functions}"
                "${MODULE_ROOT_DIR}/tools/cmock/project.yml"
                "${mock_include_list}"
                "${mock_define_list}"
        )

create_real_library(${real_name}
                    "${real_source_files}"
                    "${real_include_directories}"
                    "${mock_name}"
        )

set(utest_link_list "")
list(APPEND utest_link_list
            -l${mock_name}
            lib${real_name}.a
        )

set(utest_dep_list "")
list(APPEND utest_dep_list
            ${real_name}
        )
set(utest_name "${project_name}_command_functions_utest")
set(utest_source "${project_name}_command_functions_utest.c")
create_test(${utest_name}
            ${utest_source}
            "${utest_link_list}"
            "${utest_dep_list}"
            "${test_include_directories}"
        )
