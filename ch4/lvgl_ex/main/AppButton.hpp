#pragma once

#include "bsp_board.h"
#include "bsp_btn.h"

namespace
{
    void left_btn_pressed_down(void *param);
    void right_btn_pressed_down(void *param);
    void middle_btn_pressed_down(void *param);
    void middle_btn_released(void *param);
}

namespace app
{
    struct sAppButtonEvent
    {
        board_btn_id_t btn_id;
        button_event_t evt_id;
    };

    class AppButton
    {
    private:
        button_cb_t m_btn_cb;
        struct sAppButtonEvent btn_event;

    public:
        void init(button_cb_t cb)
        {
            m_btn_cb = cb;

            bsp_btn_register_callback(BOARD_BTN_ID_PREV, BUTTON_PRESS_DOWN, left_btn_pressed_down, this);
            bsp_btn_register_callback(BOARD_BTN_ID_NEXT, BUTTON_PRESS_DOWN, right_btn_pressed_down, this);
            bsp_btn_register_callback(BOARD_BTN_ID_ENTER, BUTTON_PRESS_DOWN, middle_btn_pressed_down, this);
            bsp_btn_register_callback(BOARD_BTN_ID_ENTER, BUTTON_PRESS_UP, middle_btn_released, this);
        }

        static AppButton &getObject(void *btn_ptr)
        {
            button_dev_t *btn_dev = reinterpret_cast<button_dev_t *>(btn_ptr);
            return *(reinterpret_cast<app::AppButton *>(btn_dev->cb_user_data));
        }

        struct sAppButtonEvent *getButtonEvent(void)
        {
            return &btn_event;
        }

        button_cb_t getCallback(void)
        {
            return m_btn_cb;
        }
    };
}

namespace
{
    void left_btn_pressed_down(void *param)
    {
        app::AppButton &app_btn = app::AppButton::getObject(param);
        app_btn.getButtonEvent()->btn_id = BOARD_BTN_ID_PREV;
        app_btn.getButtonEvent()->evt_id = BUTTON_PRESS_DOWN;
        app_btn.getCallback()(reinterpret_cast<void *>(app_btn.getButtonEvent()));
    }
    void right_btn_pressed_down(void *param)
    {
        app::AppButton &app_btn = app::AppButton::getObject(param);
        app_btn.getButtonEvent()->btn_id = BOARD_BTN_ID_NEXT;
        app_btn.getButtonEvent()->evt_id = BUTTON_PRESS_DOWN;
        app_btn.getCallback()(reinterpret_cast<void *>(app_btn.getButtonEvent()));
    }
    void middle_btn_pressed_down(void *param)
    {
        app::AppButton &app_btn = app::AppButton::getObject(param);
        app_btn.getButtonEvent()->btn_id = BOARD_BTN_ID_ENTER;
        app_btn.getButtonEvent()->evt_id = BUTTON_PRESS_DOWN;
        app_btn.getCallback()(reinterpret_cast<void *>(app_btn.getButtonEvent()));
    }
    void middle_btn_released(void *param)
    {
        app::AppButton &app_btn = app::AppButton::getObject(param);
        app_btn.getButtonEvent()->btn_id = BOARD_BTN_ID_ENTER;
        app_btn.getButtonEvent()->evt_id = BUTTON_PRESS_UP;
        app_btn.getCallback()(reinterpret_cast<void *>(app_btn.getButtonEvent()));
    }
}
