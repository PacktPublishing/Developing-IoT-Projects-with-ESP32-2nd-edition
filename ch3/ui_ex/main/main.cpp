#include "esp_log.h"
#include "bsp_board.h"

#include "AppButton.hpp"
#include "AppUi.hpp"

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
}
