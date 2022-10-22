#pragma once

#include "bsp_btn.h"
#include "bsp_board.h"

#define APPBTN_LEFT BOARD_BTN_ID_PREV
#define APPBTN_MIDDLE BOARD_BTN_ID_ENTER
#define APPBTN_RIGHT BOARD_BTN_ID_NEXT

namespace app
{
    using btn_handler_f = void (*)(void *);
    class AppButton
    {
    public:
        AppButton(int type) : m_type(type) {}

        void init(btn_handler_f btn_down_handler, btn_handler_f btn_up_handler)
        {
            bsp_btn_register_callback(static_cast<board_btn_id_t>(m_type), BUTTON_PRESS_DOWN, btn_down_handler, this);
            bsp_btn_register_callback(static_cast<board_btn_id_t>(m_type), BUTTON_PRESS_UP, btn_up_handler, this);
        }
        int getType(void) { return m_type; }

        static AppButton &getObject(void *btn_ptr)
        {
            button_dev_t *btn_dev = reinterpret_cast<button_dev_t *>(btn_ptr);
            return *(reinterpret_cast<app::AppButton *>(btn_dev->cb_user_data));
        }

    private:
        int m_type;
    };
}