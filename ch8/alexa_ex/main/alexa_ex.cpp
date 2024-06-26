#include <functional>
#include "freertos/FreeRTOS.h"
#include "freertos/task.h"

#include "AppWifiBle.hpp"
#include "AppAwsClient.hpp"
#include "AppSensorTemperature.hpp"

namespace
{
    app::AppWifiBle app_wifi;
    app::AppAwsClient app_client;
    app::AppSensorTemperature app_sensor;

    void connected_task(void *arg)
    {
        app_client.setWiFiStatus(true);
        app_sensor.start();
        vTaskDelete(nullptr);
    }
}

extern "C" void app_main()
{
    auto wifi_connected = [](esp_ip4_addr_t *addr_info) 
    {
        xTaskCreate(connected_task, "connected", 4096, nullptr, 5, nullptr);
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
