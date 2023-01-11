#include "esp_log.h"
#include "AppWifiSoftAp.hpp"
#include "AppRestClient.hpp"

#define TAG "app"

namespace
{
    app::AppWifiSoftAp app_wifi;
    app::AppRestClient rest_client;
}

extern "C" void app_main(void)
{
    auto connected = [](esp_ip4_addr_t *ip)
    {
        ESP_LOGI(TAG, "wifi connected");
        rest_client.start();
    };

    auto disconnected = []()
    {
        ESP_LOGW(TAG, "wifi disconnected");
        rest_client.pause();
    };

    rest_client.init();
    app_wifi.init(connected, disconnected);
    app_wifi.connect();
}
