
#pragma once

#include <cinttypes>
#include <vector>
#include <string>
#include <functional>
#include <cstring>

#include <esp_log.h>
#include <esp_err.h>
#include <esp_event.h>
#include <freertos/FreeRTOS.h>
#include <freertos/task.h>
#include "sdkconfig.h"

#include <esp_rmaker_core.h>
#include <esp_rmaker_standard_types.h>
#include <esp_rmaker_standard_params.h>
#include <esp_rmaker_standard_devices.h>
#include <esp_rmaker_common_events.h>
#include <esp_rmaker_utils.h>
#include <app_insights.h>
#include <esp_rmaker_ota.h>
#include <esp_rmaker_schedule.h>
#include <esp_rmaker_mqtt.h>
#include <esp_rmaker_scenes.h>

namespace app
{
    using InitDevice_f = std::function<void(esp_rmaker_device_t *, void *)>;
    using RmakerEventHandler_f = std::function<void(void *, esp_event_base_t, int32_t, void *)>;

    typedef struct
    {
        std::string node_name;
        std::string node_type;
        std::string device_name;
        std::string device_type;
        InitDevice_f init_device;
        void *init_device_arg;
    } AppNodeParams_t;

    class AppNode
    {
    private:
        static void eventHandler(void *arg, esp_event_base_t event_base, int32_t event_id, void *event_data);

        using RmakerEventHandlerItem_t = struct
        {
            RmakerEventHandler_f fn;
            void *arg;
        };
        std::vector<RmakerEventHandlerItem_t> event_handlers;

    protected:
        esp_rmaker_node_t *m_rmaker_node;
        esp_rmaker_device_t *m_device;
        bool m_connected;

        app::AppNodeParams_t m_init_params;

    public:
        AppNode() : m_rmaker_node(nullptr),
                    m_device(nullptr),
                    m_connected(false),
                    m_init_params({"", "", "", "", nullptr, nullptr})
        {
        }

        AppNode(app::AppNodeParams_t p) : m_rmaker_node(nullptr),
                                          m_device(nullptr),
                                          m_connected(false)
        {
            m_init_params = p;
        }

        virtual void init()
        {
            esp_event_handler_register(RMAKER_COMMON_EVENT, ESP_EVENT_ANY_ID, &eventHandler, this);
            esp_event_handler_register(RMAKER_OTA_EVENT, ESP_EVENT_ANY_ID, &eventHandler, this);

            esp_rmaker_time_set_timezone(CONFIG_ESP_RMAKER_DEF_TIMEZONE);
            esp_rmaker_config_t rainmaker_cfg = {
                .enable_time_sync = true,
            };
            m_rmaker_node = esp_rmaker_node_init(&rainmaker_cfg, m_init_params.node_name.c_str(), m_init_params.node_type.c_str());

            m_device = esp_rmaker_device_create(m_init_params.device_name.c_str(), m_init_params.device_type.c_str(), (void *)this);
            esp_rmaker_device_add_param(m_device, esp_rmaker_name_param_create(ESP_RMAKER_DEF_NAME_PARAM, m_init_params.device_name.c_str()));

            if (m_init_params.init_device != nullptr)
            {
                m_init_params.init_device(m_device, m_init_params.init_device_arg);
            }
            esp_rmaker_node_add_device(m_rmaker_node, m_device);

            esp_rmaker_ota_config_t ota_config;
            ota_config.server_cert = ESP_RMAKER_OTA_DEFAULT_SERVER_CERT;
            esp_rmaker_ota_enable(&ota_config, OTA_USING_PARAMS);

            esp_rmaker_system_serv_config_t system_serv_config = {
                .flags = RMAKER_EVENT_REBOOT | RMAKER_EVENT_WIFI_RESET,
                .reboot_seconds = 2,
                .reset_seconds = 2,
                .reset_reboot_seconds = 2};
            esp_rmaker_system_service_enable(&system_serv_config);

            app_insights_enable();
            esp_rmaker_schedule_enable();
            esp_rmaker_scenes_enable();
        }

        virtual void start()
        {
            esp_rmaker_start();
        }

        void addRmakerEventHandler(RmakerEventHandler_f fn, void *arg)
        {
            if (fn != nullptr)
            {
                event_handlers.push_back({fn, arg});
            }
        }

        bool isConnected() const { return m_connected; }
    }; // class end

    void AppNode::eventHandler(void *arg, esp_event_base_t event_base, int32_t event_id, void *event_data)
    {
        AppNode *obj = reinterpret_cast<AppNode *>(arg);

        if (event_base == RMAKER_COMMON_EVENT)
        {
            switch (event_id)
            {
            case RMAKER_MQTT_EVENT_CONNECTED:
                ESP_LOGI(obj->m_init_params.device_name.c_str(), "mqtt connected");
                obj->m_connected = true;
                break;
            case RMAKER_MQTT_EVENT_DISCONNECTED:
                obj->m_connected = false;
                break;
            default:
                break;
            }
        }

        for (auto &h : obj->event_handlers)
        {
            h.fn(h.arg, event_base, event_id, event_data);
        }
    } // function end
} // namespace end