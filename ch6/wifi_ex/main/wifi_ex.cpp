
#include <cinttypes>
#include "esp_log.h"

#include "AppWifi.hpp"

#define TAG "app"

namespace
{
    app::AppWifi app_wifi;
}

extern "C" void app_main(void)
{
    auto connected = [](esp_ip4_addr_t* ip)
    {
        ESP_LOGI(TAG, ">>>>>>> connected");
    };

    auto disconnected = []()
    {
        ESP_LOGW(TAG, ">>>>>>> disconnected");
    };

    app_wifi.init(connected, disconnected);
    app_wifi.connect();
}
