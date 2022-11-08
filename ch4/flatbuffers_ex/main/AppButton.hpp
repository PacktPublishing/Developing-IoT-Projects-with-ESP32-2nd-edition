#pragma once

#include "bsp_board.h"
#include "bsp_btn.h"

namespace app
{
    using btn_pressed_handler_f = void (*)(void *);

    class AppButton
    {
    public:
        void init(btn_pressed_handler_f l, btn_pressed_handler_f m)
        {
            bsp_board_init();
            bsp_btn_register_callback(BOARD_BTN_ID_PREV, BUTTON_PRESS_DOWN, l, nullptr);
            bsp_btn_register_callback(BOARD_BTN_ID_ENTER, BUTTON_PRESS_DOWN, m, nullptr);
        }
    };
}
