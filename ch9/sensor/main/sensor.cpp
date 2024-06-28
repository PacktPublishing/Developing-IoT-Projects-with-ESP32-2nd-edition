#include "bsp_board.h"

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
    app_sensor_node.init();

    // LVGL initialisation is on BSP
    bsp_display_cfg_t cfg = {
        .lvgl_port_cfg = ESP_LVGL_PORT_INIT_CONFIG(),
        .buffer_size = BSP_LCD_H_RES * CONFIG_BSP_LCD_DRAW_BUF_HEIGHT,
        .double_buffer = 0,
        .flags = {
            .buff_dma = true,
        }};
    bsp_display_start_with_config(&cfg);
    bsp_display_backlight_on();
    bsp_board_init();

    app_ui.init();

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
