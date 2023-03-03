
#pragma once

#include <cinttypes>

#include <esp_log.h>
#include <esp_event.h>
#include <freertos/FreeRTOS.h>
#include <freertos/task.h>

#include <esp_rmaker_core.h>
#include <esp_rmaker_standard_types.h>
#include <esp_rmaker_standard_params.h>
#include <esp_rmaker_standard_devices.h>
#include <esp_rmaker_ota.h>
#include <esp_rmaker_common_events.h>

namespace app
{
    class AppNode
    {
    private:
        esp_rmaker_node_t *m_rmaker_node;
        esp_rmaker_device_t *m_device;

        static void event_handler(void *arg, esp_event_base_t event_base, int32_t event_id, void *event_data);

    public:
        void init()
        {
            esp_event_handler_register(RMAKER_EVENT, ESP_EVENT_ANY_ID, &event_handler, nullptr);
            esp_event_handler_register(RMAKER_OTA_EVENT, ESP_EVENT_ANY_ID, &event_handler, nullptr);

            esp_rmaker_config_t rainmaker_cfg = {
                .enable_time_sync = false,
            };
            m_rmaker_node = esp_rmaker_node_init(&rainmaker_cfg, "A node", "OtaNode");

            m_device = esp_rmaker_device_create("OtaDevice", ESP_RMAKER_DEVICE_OTHER, nullptr);
            esp_rmaker_device_add_param(m_device, esp_rmaker_name_param_create(ESP_RMAKER_DEF_NAME_PARAM, "My device"));
            esp_rmaker_node_add_device(m_rmaker_node, m_device);

            esp_rmaker_ota_config_t ota_config = {
                .server_cert = ESP_RMAKER_OTA_DEFAULT_SERVER_CERT,
            };
            esp_rmaker_ota_enable(&ota_config, OTA_USING_PARAMS);
        }

        void start()
        {
            esp_rmaker_start();
        }
    };

    void AppNode::event_handler(void *arg, esp_event_base_t event_base, int32_t event_id, void *event_data)
    {
        if (event_base == RMAKER_EVENT)
        {
            switch (event_id)
            {
            case RMAKER_EVENT_INIT_DONE:
                ESP_LOGI(__func__, "RainMaker Initialised.");
                break;
            case RMAKER_EVENT_CLAIM_STARTED:
                ESP_LOGI(__func__, "RainMaker Claim Started.");
                break;
            case RMAKER_EVENT_CLAIM_SUCCESSFUL:
                ESP_LOGI(__func__, "RainMaker Claim Successful.");
                break;
            case RMAKER_EVENT_CLAIM_FAILED:
                ESP_LOGI(__func__, "RainMaker Claim Failed.");
                break;
            default:
                ESP_LOGW(__func__, "Unhandled RainMaker Event: %" PRIi32, event_id);
            }
        }
        else if (event_base == RMAKER_OTA_EVENT)
        {
            switch (event_id)
            {
            case RMAKER_OTA_EVENT_STARTING:
                ESP_LOGI(__func__, "Starting OTA.");
                break;
            case RMAKER_OTA_EVENT_IN_PROGRESS:
                ESP_LOGI(__func__, "OTA is in progress.");
                break;
            case RMAKER_OTA_EVENT_SUCCESSFUL:
                ESP_LOGI(__func__, "OTA successful.");
                break;
            case RMAKER_OTA_EVENT_FAILED:
                ESP_LOGI(__func__, "OTA Failed.");
                break;
            case RMAKER_OTA_EVENT_REJECTED:
                ESP_LOGI(__func__, "OTA Rejected.");
                break;
            case RMAKER_OTA_EVENT_DELAYED:
                ESP_LOGI(__func__, "OTA Delayed.");
                break;
            case RMAKER_OTA_EVENT_REQ_FOR_REBOOT:
                ESP_LOGI(__func__, "Firmware image downloaded. Please reboot your device to apply the upgrade.");
                break;
            default:
                ESP_LOGW(__func__, "Unhandled OTA Event: %" PRIi32, event_id);
                break;
            }
        }
    }
}