#pragma once

#include "bsp_board.h"

namespace app
{
    using btn_handler_f = void (*)(void *);
    class AppButton
    {
    public:
        void init(btn_handler_f l, btn_handler_f m, btn_handler_f r)
        {
            // bsp_btn_register_callback(BOARD_BTN_ID_PREV, BUTTON_PRESS_DOWN, l, NULL);
            // bsp_btn_register_callback(BOARD_BTN_ID_ENTER, BUTTON_PRESS_DOWN, m, NULL);
            // bsp_btn_register_callback(BOARD_BTN_ID_NEXT, BUTTON_PRESS_DOWN, r, NULL);
        }
    };
}