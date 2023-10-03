// https://rainmaker.espressif.com/docs/standard-types.html

#pragma once

#include <cstring>
#include <cstdint>
#include <functional>

#include "freertos/FreeRTOS.h"
#include "freertos/task.h"
#include "sdkconfig.h"

#include <esp_rmaker_core.h>
#include <esp_rmaker_standard_types.h>
#include <esp_rmaker_standard_params.h>
#include <esp_rmaker_standard_devices.h>
#include <esp_rmaker_common_events.h>
#include <esp_rmaker_utils.h>
#include <esp_rmaker_mqtt.h>

namespace app
{
    class AppRmaker
    {
    private:
        esp_rmaker_node_t *m_rmaker_node;
        esp_rmaker_device_t *m_device;
        esp_rmaker_param_t *m_cry_param;

    public:
        void init()
        {
            esp_rmaker_time_set_timezone(CONFIG_ESP_RMAKER_DEF_TIMEZONE);
            esp_rmaker_config_t rainmaker_cfg = {
                .enable_time_sync = true,
            };
            m_rmaker_node = esp_rmaker_node_init(&rainmaker_cfg, "Baby node", "esp.node.sensor");

            m_device = esp_rmaker_device_create("Cry sensor", "esp.device.sensor", (void *)this);
            esp_rmaker_device_add_param(m_device, esp_rmaker_name_param_create(ESP_RMAKER_DEF_NAME_PARAM, "Cry sensor"));

            m_cry_param = esp_rmaker_param_create("Baby crying", "esp.param.toggle", esp_rmaker_bool(false), PROP_FLAG_READ);
            esp_rmaker_param_add_ui_type(m_cry_param, ESP_RMAKER_UI_TOGGLE);
            esp_rmaker_device_add_param(m_device, m_cry_param);
            esp_rmaker_device_assign_primary_param(m_device, m_cry_param);

            esp_rmaker_node_add_device(m_rmaker_node, m_device);
        }

        void start()
        {
            esp_rmaker_start();
        }

        void update(bool state)
        {
            esp_rmaker_param_update_and_report(m_cry_param, esp_rmaker_bool(state));
            if (state)
            {
                esp_rmaker_raise_alert("crying");
            }
        }
    };

}
