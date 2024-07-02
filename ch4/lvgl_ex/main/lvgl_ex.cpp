#include "bsp_board.h"

#include "AppUi.hpp"
#include "AppButton.hpp"

namespace
{
    app::AppUi m_app_ui;
    app::AppButton m_app_btn;
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

    auto btn_evt_handler = [](app::sAppButtonEvent &e)
    {
        m_app_ui.buttonEventHandler(e);
    };

    m_app_ui.init();
    m_app_btn.init(btn_evt_handler);
}
