
#include "AppDriver.hpp"
#include "AppSensorNode.hpp"
#include "AppUi.hpp"

namespace
{
    app::AppDriver app_driver;
    app::AppSensorNode app_sensor_node;
    app::AppUi app_ui;
}

extern "C" void app_main(void)
{
    app_driver.init();
    app_ui.init();
    app_sensor_node.init();

    auto sensor_reading_handler = [](const app::SensorReading_t &r) -> void
    {
        app_ui.updateSensorReading(r);
    };
    app_sensor_node.setReadingCb(sensor_reading_handler);

    auto mqtt_state_handler = [](void *arg, esp_event_base_t event_base, int32_t event_id, void *event_data) -> void
    {
        if (event_base != RMAKER_COMMON_EVENT)
        {
            return;
        }
        switch (event_id)
        {
        case RMAKER_MQTT_EVENT_CONNECTED:
            app_ui.updateMqttState(true);
            break;
        case RMAKER_MQTT_EVENT_DISCONNECTED:
            app_ui.updateMqttState(false);
            break;
        default:
            break;
        }
    };
    app_sensor_node.addRmakerEventHandler(mqtt_state_handler, nullptr);

    app_ui.start();
    app_sensor_node.start();
    app_driver.start();
}
