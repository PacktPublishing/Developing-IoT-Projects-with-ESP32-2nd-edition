set(srcs "src/work_queue.c" "src/factory.c" "src/time.c" "src/timezone.c" "src/utils.c")
set(priv_req "mqtt" "nvs_flash")

#if(CONFIG_ESP_RMAKER_LIB_ESP_MQTT)
    list(APPEND srcs "src/esp-mqtt/esp-mqtt-glue.c")
#endif()

idf_component_register(SRCS ${srcs}
                       INCLUDE_DIRS "include"
                       PRIV_INCLUDE_DIRS
                       REQUIRES
                       PRIV_REQUIRES ${priv_req})
