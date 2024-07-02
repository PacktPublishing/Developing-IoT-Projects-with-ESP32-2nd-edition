idf_component_register(SRCS "app_main.c"
                    INCLUDE_DIRS ".")
if (CONFIG_ESP_INSIGHTS_TRANSPORT_HTTPS)
    target_add_binary_data(${COMPONENT_TARGET} "insights_auth_key.txt" TEXT)
endif()
