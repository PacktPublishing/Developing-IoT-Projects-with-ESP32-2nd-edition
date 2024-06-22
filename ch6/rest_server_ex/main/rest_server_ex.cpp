#include "esp_log.h"
#include "AppWifiBle.hpp"
#include "AppRestServer.hpp"

#define TAG "app"

namespace
{
    app::AppWifiBle app_wifi;
    app::AppRestServer rest_server;
}

extern "C" void app_main(void)
{
    auto connected = [](esp_ip4_addr_t *ip)
    {
        ESP_LOGI(TAG, "wifi connected");
        rest_server.start();
    };

    auto disconnected = []()
    {
        ESP_LOGW(TAG, "wifi disconnected");
        rest_server.stop();
    };

    rest_server.init();
    app_wifi.init(connected, disconnected);
    app_wifi.connect();
}