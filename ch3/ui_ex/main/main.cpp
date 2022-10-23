#include "bsp_board.h"

#include "AppButton.hpp"
#include "AppUi.hpp"

#define APPBTN_MIDDLE_TEXT "Middle button"
#define APPBTN_LEFT_TEXT "Left button"
#define APPBTN_RIGHT_TEXT "Right button"

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

    auto btn_down_handler = [](void *btn_ptr)
    {
        app::AppButton &btn = app::AppButton::getObject(btn_ptr);
        switch (btn.getType())
        {
        case APPBTN_MIDDLE:
            m_app_ui.setLabelText(APPBTN_MIDDLE_TEXT " down");
            break;
        case APPBTN_LEFT:
            m_app_ui.setLabelText(APPBTN_LEFT_TEXT " down");
            break;
        case APPBTN_RIGHT:
            m_app_ui.setLabelText(APPBTN_RIGHT_TEXT " down");
            break;

        default:
            break;
        }
    };

    auto btn_up_handler = [](void *btn_ptr)
    {
        app::AppButton &btn = app::AppButton::getObject(btn_ptr);
        switch (btn.getType())
        {
        case APPBTN_MIDDLE:
            m_app_ui.setLabelText(APPBTN_MIDDLE_TEXT " up");
            break;
        case APPBTN_LEFT:
            m_app_ui.setLabelText(APPBTN_LEFT_TEXT " up");
            break;
        case APPBTN_RIGHT:
            m_app_ui.setLabelText(APPBTN_RIGHT_TEXT " up");
            break;

        default:
            break;
        }
    };

    m_btn_middle.init(btn_down_handler, btn_up_handler);
    m_btn_left.init(btn_down_handler, btn_up_handler);
    m_btn_right.init(btn_down_handler, btn_up_handler);
    m_app_ui.init();
}
