#pragma once

#include "bsp_board.h"

#define APPBTN_LEFT BOARD_BTN_ID_PREV
#define APPBTN_MIDDLE BOARD_BTN_ID_ENTER
#define APPBTN_RIGHT BOARD_BTN_ID_NEXT

namespace app
{
    class AppButton
    {
    private:
        int m_type;
    public:
        AppButton(int type) : m_type(type) {}
        int getType(void) { return m_type; }

        void init(button_cb_t btn_down_handler, button_cb_t btn_up_handler)
        {
            bsp_btn_register_callback(static_cast<bsp_button_t>(m_type), BUTTON_PRESS_DOWN, btn_down_handler, this);
            bsp_btn_register_callback(static_cast<bsp_button_t>(m_type), BUTTON_PRESS_UP, btn_up_handler, this);
        }

    };
}