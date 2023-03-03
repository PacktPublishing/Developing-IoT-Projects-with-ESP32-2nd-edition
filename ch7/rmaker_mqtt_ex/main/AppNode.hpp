
#pragma once

#include <cinttypes>
#include <map>
#include <string>

#include <esp_log.h>
#include <esp_event.h>
#include <freertos/FreeRTOS.h>
#include <freertos/task.h>

#include <esp_rmaker_core.h>
#include <esp_rmaker_standard_types.h>
#include <esp_rmaker_standard_params.h>
#include <esp_rmaker_standard_devices.h>
#include <esp_rmaker_common_events.h>
#include <esp_rmaker_utils.h>
#include <app_insights.h>

#include "sdkconfig.h"
#include "AppSensorClient.hpp"

namespace app
{
    class AppNode : public AppSensorClient
    {
    private:
        esp_rmaker_node_t *m_rmaker_node;
        esp_rmaker_device_t *m_device;
        esp_rmaker_param_t *m_light_param;
        bool m_connected{false};

        static void event_handler(void *arg, esp_event_base_t event_base, int32_t event_id, void *event_data);

    public:
        void init()
        {
            esp_event_handler_register(RMAKER_COMMON_EVENT, ESP_EVENT_ANY_ID, &event_handler, this);

            esp_rmaker_time_set_timezone(CONFIG_ESP_RMAKER_DEF_TIMEZONE);
            esp_rmaker_config_t rainmaker_cfg = {
                .enable_time_sync = true,
            };
            m_rmaker_node = esp_rmaker_node_init(&rainmaker_cfg, "A light-sensor node", "LightSensorNode");

            m_device = esp_rmaker_device_create("LightSensorDevice", ESP_RMAKER_DEVICE_LIGHT, nullptr);
            esp_rmaker_device_add_param(m_device, esp_rmaker_name_param_create(ESP_RMAKER_DEF_NAME_PARAM, "Light sensor"));

            m_light_param = esp_rmaker_param_create("LightParam",
                                                    "app.lightlevel",
                                                    esp_rmaker_int(0),
                                                    PROP_FLAG_READ | PROP_FLAG_TIME_SERIES);
            esp_rmaker_param_add_ui_type(m_light_param, ESP_RMAKER_UI_TEXT);
            esp_rmaker_device_add_param(m_device, m_light_param);
            esp_rmaker_device_assign_primary_param(m_device, m_light_param);

            esp_rmaker_node_add_device(m_rmaker_node, m_device);

            app_insights_enable();
        }

        void start()
        {
            esp_rmaker_start();
        }

        void update(uint32_t light_level) override
        {
            if (m_connected)
            {
                esp_rmaker_param_update_and_report(m_light_param, esp_rmaker_int(light_level));
            }
        }
    };

    void AppNode::event_handler(void *arg, esp_event_base_t event_base, int32_t event_id, void *event_data)
    {
        AppNode *obj = reinterpret_cast<AppNode *>(arg);

        switch (event_id)
        {
        case RMAKER_MQTT_EVENT_CONNECTED:
            obj->m_connected = true;
            break;
        case RMAKER_MQTT_EVENT_DISCONNECTED:
            obj->m_connected = false;
            break;
        default:
            break;
        }
    }
}