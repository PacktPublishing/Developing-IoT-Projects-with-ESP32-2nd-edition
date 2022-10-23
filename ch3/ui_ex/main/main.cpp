#include "esp_log.h"
#include "bsp_board.h"
#include "bsp_lcd.h"

#include "AppButton.hpp"
#include "AppUi.hpp"

#define APPBTN_LEFT_TEXT "BTN_LEFT"
#define APPBTN_MIDDLE_TEXT "BTN_MIDDLE"
#define APPBTN_RIGHT_TEXT "BTN_RIGHT"

namespace
{
    app::AppButton m_btn_middle{APPBTN_MIDDLE};
    app::AppButton m_btn_left{APPBTN_LEFT};
    app::AppButton m_btn_right{APPBTN_RIGHT};
    app::AppUi m_app_ui;

    static const constexpr char *TAG{"app"};
}

extern "C" void app_main(void)
{
    bsp_board_init();

    auto btn_down = [](void *btn_ptr)
    {
        app::AppButton &btn = app::AppButton::getObject(btn_ptr);
        switch (btn.getType())
        {
        case APPBTN_MIDDLE:
            m_app_ui.setLabelText(APPBTN_MIDDLE_TEXT " pressed");
            break;
        case APPBTN_LEFT:
            m_app_ui.setLabelText(APPBTN_LEFT_TEXT " pressed");
            break;
        case APPBTN_RIGHT:
            m_app_ui.setLabelText(APPBTN_RIGHT_TEXT " pressed");
            break;

        default:
            break;
        }
        ESP_LOGI(TAG, "%d down", btn.getType());
    };

    auto btn_up = [](void *btn_ptr)
    {
        app::AppButton &btn = app::AppButton::getObject(btn_ptr);
        ESP_LOGI(TAG, "%d up", btn.getType());
    };

    m_btn_middle.init(btn_down, btn_up);
    m_btn_left.init(btn_down, btn_up);
    m_btn_right.init(btn_down, btn_up);
    m_app_ui.init();
    bsp_lcd_set_backlight(true); // Turn on the backlight after gui initialize
}
