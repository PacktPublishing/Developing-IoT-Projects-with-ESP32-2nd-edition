#pragma once

#include <string>
#include "freertos/FreeRTOS.h"
#include "freertos/task.h"
#include "json.hpp"
#include "AppEsp32C3Bsp.hpp"

#include "esp_http_server.h"

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

    class AppRestServer
    {
    private:
        AppEsp32C3Bsp m_bsp;
        bool m_toggle_btn;
        sSensorConfig m_config;
        sSensorData m_data;

        httpd_handle_t m_server = nullptr;

        static esp_err_t handleDataGet(httpd_req_t *req);
        static esp_err_t handleConfigPut(httpd_req_t *req);
        static void handleBtn(void *arg);

    public:
        void init(void)
        {
            m_config.enabled = true;
            m_config.name = "sensor-0";
            m_toggle_btn = false;
            m_data.name = m_config.name;
            m_data.button = m_toggle_btn ? "on" : "off";

            m_bsp.init();
            auto fn = [](void *arg)
            {
                handleBtn(arg);
            };
            m_bsp.addButtonHandler(button_cb_type_t::BUTTON_CB_RELEASE, fn, this);
        }

        void start(void)
        {
            httpd_config_t config = HTTPD_DEFAULT_CONFIG();
            config.stack_size = 6000;
            httpd_start(&m_server, &config);

            httpd_uri_t data_ep = {
                .uri = "/data",
                .method = HTTP_GET,
                .handler = handleDataGet,
                .user_ctx = this};
            httpd_register_uri_handler(m_server, &data_ep);

            httpd_uri_t config_ep = {
                .uri = "/config",
                .method = HTTP_PUT,
                .handler = handleConfigPut,
                .user_ctx = this};
            httpd_register_uri_handler(m_server, &config_ep);
        }

        void stop(void)
        {
            httpd_stop(m_server);
            m_server = nullptr;
        }
    };

    esp_err_t AppRestServer::handleDataGet(httpd_req_t *req)
    {
        AppRestServer *obj = (AppRestServer *)(req->user_ctx);

        if (obj->m_config.enabled)
        {
            obj->m_data.button = obj->m_toggle_btn ? "on" : "off";
            nlohmann::json data_json = obj->m_data;
            std::string data_str = data_json.dump();
            httpd_resp_send(req, data_str.c_str(), data_str.length());
        }
        else
        {
            httpd_resp_send(req, nullptr, 0);
        }
        return ESP_OK;
    }

    esp_err_t AppRestServer::handleConfigPut(httpd_req_t *req)
    {
        AppRestServer *obj = (AppRestServer *)(req->user_ctx);
        char buffer[256] = {0};

        httpd_req_recv(req, buffer, sizeof(buffer));
        nlohmann::json req_json = nlohmann::json::parse(buffer, nullptr, false);
        if (req_json.is_discarded())
        {
            httpd_resp_send_err(req, HTTPD_400_BAD_REQUEST, "not a JSON");
        }
        else
        {
            nlohmann::json config_json = obj->m_config;
            config_json.merge_patch(req_json);
            obj->m_config = config_json;
            obj->m_data.name = obj->m_config.name;
            httpd_resp_send(req, NULL, 0);
        }

        return ESP_OK;
    }

    void AppRestServer::handleBtn(void *arg)
    {
        AppRestServer *obj = reinterpret_cast<AppRestServer *>(arg);
        obj->m_toggle_btn = !obj->m_toggle_btn;
    }
}