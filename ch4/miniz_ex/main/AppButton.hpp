#pragma once

#include "bsp_board.h"

namespace app
{
    class AppButton
    {
    public:
        void init(button_cb_t l, button_cb_t m)
        {
            bsp_i2c_init();
            bsp_board_init();
            bsp_btn_register_callback(BOARD_BTN_ID_PREV, BUTTON_PRESS_DOWN, l, nullptr);
            bsp_btn_register_callback(BOARD_BTN_ID_ENTER, BUTTON_PRESS_DOWN, m, nullptr);
        }
    };
}
