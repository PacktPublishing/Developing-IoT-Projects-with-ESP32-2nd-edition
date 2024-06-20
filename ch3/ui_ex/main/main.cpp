#include "bsp_board.h"

#include "AppButton.hpp"
#include "AppUi.hpp"

namespace
{
    app::AppButton m_btn_left{APPBTN_LEFT};
    app::AppButton m_btn_middle{APPBTN_MIDDLE};
    app::AppButton m_btn_right{APPBTN_RIGHT};
    app::AppUi m_app_ui;
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

    auto btn_down_handler = [](void *btn_ptr, void *user_data)
    {
        app::AppButton &btn = *(reinterpret_cast<app::AppButton *>(user_data));
        switch (btn.getType())
        {
        case APPBTN_LEFT:
            m_app_ui.setLabelText("Left button down");
            break;
        case APPBTN_MIDDLE:
            m_app_ui.setLabelText("Middle button down");
            break;
        case APPBTN_RIGHT:
            m_app_ui.setLabelText("Right button down");
            break;
        default:
            break;
        }
    };

    auto btn_up_handler = [](void *btn_ptr, void *user_data)
    {
        m_app_ui.setLabelText("Button released");
    };

    m_btn_left.init(btn_down_handler, btn_up_handler);
    m_btn_middle.init(btn_down_handler, btn_up_handler);
    m_btn_right.init(btn_down_handler, btn_up_handler);
    m_app_ui.init();
}
