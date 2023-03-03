
#pragma once

#include <string>
#include "freertos/FreeRTOS.h"
#include "freertos/task.h"
#include "AppEsp32C3Bsp.hpp"
#include "esp_http_client.h"
#include "sdkconfig.h"
#include "esp_ota_ops.h"
#include "esp_https_ota.h"
#include "esp_log.h"

#define FILE_SERVER_URL "https://" CONFIG_FILE_SERVER_IP ":" CONFIG_FILE_SERVER_PORT

extern const uint8_t server_cert_pem_start[] asm("_binary_cert_pem_start");
extern const uint8_t server_cert_pem_end[] asm("_binary_cert_pem_end");

namespace app
{
    class AppOtaClient
    {
    private:
        TaskHandle_t m_ota_task;
        static void otaTaskFunc(void *arg);

        static constexpr char *INFO_ENDPOINT{FILE_SERVER_URL "/info"};
        static constexpr char *FILE_SERVER_STATIC{FILE_SERVER_URL "/static/"};

        std::string getInfo(char *buffer, size_t buffer_len);
        void doOtaUpdate(char *buffer, size_t buffer_len, const std::string &filename);
        static esp_err_t handleHttpEvents(esp_http_client_event_t *evt);

        bool m_ota_done;

    public:
        void init(void)
        {
            m_ota_done = false;
            xTaskCreate(otaTaskFunc, "ota", 8192, this, 5, &m_ota_task);
            vTaskSuspend(m_ota_task);
        }

        void start(void)
        {
            vTaskResume(m_ota_task);
        }

        void pause(void)
        {
            vTaskSuspend(m_ota_task);
        }

        bool isOtaDone(void) const
        {
            return m_ota_done;
        }
    };

    void AppOtaClient::otaTaskFunc(void *arg)
    {
        AppOtaClient *obj = reinterpret_cast<AppOtaClient *>(arg);
        static char buffer[8192];

        while (true)
        {
            vTaskDelay(pdMS_TO_TICKS(10000));

            std::string filename = obj->getInfo(buffer, sizeof(buffer));
            if (!filename.empty())
            {
                obj->doOtaUpdate(buffer, sizeof(buffer), filename);
            }
        }
    }

    std::string AppOtaClient::getInfo(char *buffer, size_t buffer_len)
    {
        memset(buffer, 0, buffer_len);

        esp_http_client_config_t client_config = {
            .url = INFO_ENDPOINT,
            .cert_pem = (const char *)server_cert_pem_start,
            .method = HTTP_METHOD_GET,
            .event_handler = handleHttpEvents,
            .transport_type = HTTP_TRANSPORT_OVER_SSL,
            .user_data = buffer,
            .skip_cert_common_name_check = true};

        esp_http_client_handle_t client = esp_http_client_init(&client_config);

        std::string filename{""};
        if (esp_http_client_perform(client) == ESP_OK)
        {
            filename = std::string(buffer);
        }
        esp_http_client_cleanup(client);

        return filename;
    }

    esp_err_t AppOtaClient::handleHttpEvents(esp_http_client_event_t *evt)
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

    void AppOtaClient::doOtaUpdate(char *buffer, size_t buffer_len, const std::string &filename)
    {
        std::string file_url{std::string(FILE_SERVER_STATIC) + filename};

        esp_http_client_config_t client_config = {
            .url = file_url.c_str(),
            .cert_pem = (const char *)server_cert_pem_start,
            .method = HTTP_METHOD_GET,
            .event_handler = nullptr,
            .transport_type = HTTP_TRANSPORT_OVER_SSL,
            .user_data = buffer,
            .skip_cert_common_name_check = true};

        esp_https_ota_config_t ota_config = {
            .http_config = &client_config,
            .partial_http_download = true,
            .max_http_request_size = (int)buffer_len};

        const esp_partition_t *running = esp_ota_get_running_partition();
        esp_app_desc_t running_app_info;
        esp_ota_get_partition_description(running, &running_app_info);

        esp_https_ota_handle_t https_ota_handle{nullptr};
        esp_https_ota_begin(&ota_config, &https_ota_handle);

        esp_app_desc_t app_desc;
        if (esp_https_ota_get_img_desc(https_ota_handle, &app_desc) != ESP_OK ||
            memcmp(app_desc.version, running_app_info.version, sizeof(app_desc.version)) == 0)
        {
            esp_https_ota_abort(https_ota_handle);
            return;
        }

        int img_size = esp_https_ota_get_image_size(https_ota_handle);
        while (esp_https_ota_perform(https_ota_handle) == ESP_ERR_HTTPS_OTA_IN_PROGRESS)
        {
            int read_size = esp_https_ota_get_image_len_read(https_ota_handle);
            ESP_LOGI(__func__, "%%%0.1f (bytes %d/%d)", ((float)read_size) * 100 / img_size, read_size, img_size);
        }

        if (esp_https_ota_is_complete_data_received(https_ota_handle) != true)
        {
            esp_https_ota_abort(https_ota_handle);
        }
        else
        {
            if (esp_https_ota_finish(https_ota_handle) == ESP_OK)
            {
                m_ota_done = true;
                vTaskDelete(nullptr);
            }
            else
            {
                esp_https_ota_abort(https_ota_handle);
            }
        }
    }

}
