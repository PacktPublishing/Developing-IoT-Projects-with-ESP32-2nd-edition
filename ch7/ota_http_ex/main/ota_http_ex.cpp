#include "esp_log.h"
#include "AppWifiBle.hpp"
#include "AppOtaClient.hpp"

#include "freertos/FreeRTOS.h"
#include "freertos/task.h"

#define TAG "app"

namespace
{
    app::AppWifiBle app_wifi;
    app::AppOtaClient ota_client;
}

extern "C" void app_main(void)
{
    auto connected = [](esp_ip4_addr_t *ip)
    {
        ESP_LOGI(TAG, "wifi connected");
        ota_client.start();
    };

    auto disconnected = []()
    {
        ESP_LOGW(TAG, "wifi disconnected");
        if (!ota_client.isOtaDone())
        {
            ota_client.pause();
        }
    };

    ota_client.init();
    app_wifi.init(connected, disconnected);
    app_wifi.connect();

    while (1)
    {
        vTaskDelay(pdMS_TO_TICKS(2000));
        if (ota_client.isOtaDone())
        {
            esp_restart();
        }
    }
}
