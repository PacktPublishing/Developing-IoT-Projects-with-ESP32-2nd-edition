#pragma once

#include "bsp_board.h"
#include "bsp_btn.h"

namespace app
{
    class AppButton
    {
    public:
        void init(button_cb_t left, button_cb_t middle, button_cb_t right)
        {
            bsp_btn_register_callback(BOARD_BTN_ID_PREV, BUTTON_PRESS_DOWN, left, nullptr);
            bsp_btn_register_callback(BOARD_BTN_ID_ENTER, BUTTON_PRESS_DOWN, middle, nullptr);
            bsp_btn_register_callback(BOARD_BTN_ID_NEXT, BUTTON_PRESS_DOWN, right, nullptr);
        }
    };
}
