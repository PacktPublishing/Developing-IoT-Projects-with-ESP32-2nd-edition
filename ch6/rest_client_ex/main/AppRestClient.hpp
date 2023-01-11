
#pragma once

#include <string>
#include "freertos/FreeRTOS.h"
#include "freertos/task.h"
#include "json.hpp"
#include "AppEsp32C3Bsp.hpp"

#include "esp_http_client.h"

namespace app
{
    struct sSensorConfig
    {
        std::string name;
        bool enabled;
    };
    NLOHMANN_DEFINE_TYPE_NON_INTRUSIVE(sSensorConfig, name, enabled);

    struct sSensorData
    {
        std::string name;
        std::string button;
    };
    NLOHMANN_DEFINE_TYPE_NON_INTRUSIVE(sSensorData, name, button);

    class AppRestClient
    {
    private:
        AppEsp32C3Bsp m_bsp;
        bool m_toggle_btn;
        TaskHandle_t m_publish_task;

        static esp_err_t handleHttpEvents(esp_http_client_event_t *evt);
        static void publishSensorState(void *arg);
        static void handleBtn(void *arg);

    public:
        void init(void)
        {
            m_bsp.init();
            auto fn = [](void *arg)
            {
                handleBtn(arg);
            };
            m_bsp.addButtonHandler(button_cb_type_t::BUTTON_CB_RELEASE, fn, this);
            xTaskCreate(publishSensorState, "publish", 4096, this, 5, &m_publish_task);
            vTaskSuspend(m_publish_task);
        }

        void start(void)
        {
            vTaskResume(m_publish_task);
        }

        void pause(void)
        {
            vTaskSuspend(m_publish_task);
        }
    };

    void AppRestClient::publishSensorState(void *arg)
    {
        AppRestClient *obj = reinterpret_cast<AppRestClient *>(arg);
        std::string host{std::string("http://" CONFIG_REST_SERVER_IP ":") + std::to_string(CONFIG_REST_SERVER_PORT)};
        std::string config_url{host + "/config"};
        std::string data_url{host + "/data"};
        static char buffer[1024];

        while (true)
        {
            vTaskDelay(pdMS_TO_TICKS(3000));

            esp_http_client_config_t client_config = {
                .url = config_url.c_str(),
                .method = HTTP_METHOD_GET,
                .event_handler = handleHttpEvents,
                .transport_type = HTTP_TRANSPORT_OVER_TCP,
                .user_data = buffer};

            esp_http_client_handle_t client = esp_http_client_init(&client_config);
            esp_http_client_perform(client);

            sSensorConfig sensor_config = nlohmann::json::parse(buffer);
            if (sensor_config.enabled)
            {
                esp_http_client_set_url(client, data_url.c_str());
                esp_http_client_set_method(client, HTTP_METHOD_PUT);
                esp_http_client_set_header(client, "Content-Type", "application/json");

                sSensorData data{.name = sensor_config.name, .button = obj->m_toggle_btn ? "on" : "off"};
                nlohmann::json data_json = data;
                std::string data_str = data_json.dump();
                esp_http_client_set_post_field(client, data_str.c_str(), data_str.length());
                esp_http_client_perform(client);
            }

            esp_http_client_cleanup(client);
        }
    }

    esp_err_t AppRestClient::handleHttpEvents(esp_http_client_event_t *evt)
    {
        switch (evt->event_id)
        {
        case HTTP_EVENT_ON_DATA:
            memcpy(evt->user_data, evt->data, evt->data_len);
        default:
            break;
        }
        return ESP_OK;
    }

    void AppRestClient::handleBtn(void *arg)
    {
        AppRestClient *obj = reinterpret_cast<AppRestClient *>(arg);
        obj->m_toggle_btn = !obj->m_toggle_btn;
    }

}
