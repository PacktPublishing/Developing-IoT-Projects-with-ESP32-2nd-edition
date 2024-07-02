#include "bsp_board.h"

#include "AppSine.hpp"
#include "AppUi.hpp"

namespace
{
    app::AppSine app_sine;
    app::AppUi app_ui;
}

extern "C" void app_main(void)
{
    bsp_i2c_init();

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
    app_sine.init(&app_ui);

    app_sine.run();
}