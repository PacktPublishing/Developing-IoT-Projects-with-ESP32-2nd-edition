#pragma once

#include "bsp_board.h"

namespace app
{
    class AppButton
    {
    public:
        void init(button_cb_t l, button_cb_t m, button_cb_t r)
        {
            bsp_btn_register_callback(BOARD_BTN_ID_PREV, BUTTON_PRESS_DOWN, l, NULL);
            bsp_btn_register_callback(BOARD_BTN_ID_ENTER, BUTTON_PRESS_DOWN, m, NULL);
            bsp_btn_register_callback(BOARD_BTN_ID_NEXT, BUTTON_PRESS_DOWN, r, NULL);
        }
    };
}