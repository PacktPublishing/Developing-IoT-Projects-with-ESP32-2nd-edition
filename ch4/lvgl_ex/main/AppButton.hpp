#pragma once

#include "bsp_board.h"
#include "bsp_btn.h"

namespace
{
    template <board_btn_id_t I, button_event_t E>
    void button_event_handler(void *param);
}

namespace app
{
    struct sAppButtonEvent
    {
        board_btn_id_t btn_id;
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

        static AppButton &getObject(void *btn_ptr)
        {
            button_dev_t *btn_dev = reinterpret_cast<button_dev_t *>(btn_ptr);
            return *(reinterpret_cast<app::AppButton *>(btn_dev->cb_user_data));
        }

        void runCallback(sAppButtonEvent &e)
        {
            m_btn_cb(e);
        }
    };
}

namespace
{
    template <board_btn_id_t I, button_event_t E>
    void button_event_handler(void *btn_ptr)
    {
        app::AppButton &app_btn = app::AppButton::getObject(btn_ptr);
        app::sAppButtonEvent e{I, E};
        app_btn.runCallback(e);
    }
}
