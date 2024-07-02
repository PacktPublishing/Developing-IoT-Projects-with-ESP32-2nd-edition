#include <functional>
#include "AppWifiBle.hpp"
#include "AppAwsClient.hpp"
#include "AppSensor.hpp"

namespace
{
    app::AppWifiBle app_wifi;
    app::AppAwsClient app_client;
    app::AppSensor app_sensor;
}

extern "C" void app_main()
{
    auto wifi_connected = [](esp_ip4_addr_t *addr_info)
    {
        app_client.setWiFiStatus(true);
        app_sensor.start();
    };

    auto wifi_disconnected = [](void)
    {
        app_client.setWiFiStatus(false);
    };

    app_wifi.init(wifi_connected, wifi_disconnected);
    app_client.init();
    app_sensor.init(&app_client, 5);

    app_wifi.connect();
}
