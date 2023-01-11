#include "esp_log.h"
#include "AppWifiSoftAp.hpp"
#include "AppMqtt.hpp"
#include "AppSensorDevkit.hpp"

#define TAG "app"

namespace
{
    app::AppWifiSoftAp app_wifi;
    app::AppSensorDevkit app_sensor;
    app::AppMqtt app_mqtt{&app_sensor};
}

extern "C" void app_main(void)
{
    auto wifi_connected = [](esp_ip4_addr_t *ip)
    {
        ESP_LOGI(TAG, "wifi connected");
        app_mqtt.start();
    };

    auto wifi_disconnected = []()
    {
        ESP_LOGW(TAG, "wifi disconnected");
    };

    auto mqtt_cb = [](app::MqttEventData_t event)
    {
        switch (event.id)
        {
        case MQTT_EVENT_ERROR:
            ESP_LOGW(TAG, "mqtt error");
            break;
        case MQTT_EVENT_CONNECTED:
            ESP_LOGI(TAG, "mqtt connected");
            break;
        case MQTT_EVENT_DISCONNECTED:
            ESP_LOGW(TAG, "mqtt disconnected");
            break;
        default:
            break;
        }
    };

    app_sensor.init();
    app_mqtt.init(mqtt_cb);
    app_wifi.init(wifi_connected, wifi_disconnected);
    app_wifi.connect();
}