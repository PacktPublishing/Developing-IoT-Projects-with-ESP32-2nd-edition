# ESP Insights
set(srcs "src/esp_insights.c"
        "src/esp_insights_mqtt.c"
        "src/esp_insights_client_data.c"
        "src/esp_insights_encoder.c"
        "src/esp_insights_cbor_encoder.c")
set(priv_req esp_diagnostics cbor rmaker_common esptool_py espcoredump rtc_store nvs_flash)

idf_component_register(SRCS ${srcs}
                       INCLUDE_DIRS "include"
                       PRIV_INCLUDE_DIRS "src"
                       REQUIRES
                       PRIV_REQUIRES ${priv_req})

target_add_binary_data(${COMPONENT_TARGET} "server_certs/mqtt_server.crt" TEXT)

# Added just to automatically trigger re-runs of CMake
git_describe(ESP_INSIGHTS_VERSION ${COMPONENT_DIR})
message("ESP Insights Project commit: " ${INSIGHTS_VERSION})
