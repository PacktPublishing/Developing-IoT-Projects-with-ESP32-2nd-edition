#pragma once

#include "bsp_board.h"

namespace
{
    template <bsp_button_t I, button_event_t E>
    void button_event_handler(void *param, void *user_data);
}

namespace app
{
    struct sAppButtonEvent
    {
        bsp_button_t btn_id;
        button_event_t evt_id;
    };

    using fAppButtonCallback = void (*)(sAppButtonEvent &);

    class AppButton
    {
    private:
        fAppButtonCallback m_btn_cb;

    public:
        void init(fAppButtonCallback cb)
        {
            m_btn_cb = cb;
            bsp_btn_register_callback(BOARD_BTN_ID_PREV, BUTTON_PRESS_DOWN,
                                      button_event_handler<BOARD_BTN_ID_PREV, BUTTON_PRESS_DOWN>, this);
            bsp_btn_register_callback(BOARD_BTN_ID_NEXT, BUTTON_PRESS_DOWN,
                                      button_event_handler<BOARD_BTN_ID_NEXT, BUTTON_PRESS_DOWN>, this);
            bsp_btn_register_callback(BOARD_BTN_ID_ENTER, BUTTON_PRESS_DOWN,
                                      button_event_handler<BOARD_BTN_ID_ENTER, BUTTON_PRESS_DOWN>, this);
            bsp_btn_register_callback(BOARD_BTN_ID_ENTER, BUTTON_PRESS_UP,
                                      button_event_handler<BOARD_BTN_ID_ENTER, BUTTON_PRESS_UP>, this);
        }

        void runCallback(sAppButtonEvent &e)
        {
            m_btn_cb(e);
        }
    };
}

namespace
{
    template <bsp_button_t I, button_event_t E>
    void button_event_handler(void *btn_ptr, void *user_data)
    {
        app::AppButton &app_btn = *(reinterpret_cast<app::AppButton *>(user_data));
        app::sAppButtonEvent e{I, E};
        app_btn.runCallback(e);
    }
}
