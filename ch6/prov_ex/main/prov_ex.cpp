#include "esp_log.h"
#include "AppWifiSoftAp.hpp"
#include "AppWifiBle.hpp"

#define TAG "app"

namespace
{
#if CONFIG_PROV_METHOD == 0
    app::AppWifiSoftAp *app_wifi = new app::AppWifiSoftAp();
#else
    app::AppWifiBle *app_wifi = new app::AppWifiBle();
#endif
}

extern "C" void app_main(void)
{
    auto connected = [](esp_ip4_addr_t *ip)
    {
        ESP_LOGI(TAG, ">>>>>>> connected");
    };

    auto disconnected = []()
    {
        ESP_LOGW(TAG, ">>>>>>> disconnected");
    };

    app_wifi->init(connected, disconnected);
    app_wifi->connect();
}
