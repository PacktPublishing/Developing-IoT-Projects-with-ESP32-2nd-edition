#pragma once

#include "freertos/FreeRTOS.h"
#include "freertos/queue.h"

#include "bsp_board.h"
#include "bsp_btn.h"

#include "esp_log.h"

namespace app
{
    enum class eBtnEvent
    {
        L_PRESSED,
        L_RELEASED,
        M_CLICK,
        M_DCLICK,
        R_PRESSED,
        R_RELEASED
    };
}

namespace
{
    template <app::eBtnEvent>
    void button_event_handler(void *param);
}

namespace app
{
    class AppButton
    {
    private:
        QueueHandle_t m_event_queue = NULL;

    public:
        void init(void)
        {
            m_event_queue = xQueueCreate(10, sizeof(app::eBtnEvent));

            bsp_btn_register_callback(BOARD_BTN_ID_PREV, BUTTON_PRESS_DOWN,
                                      button_event_handler<app::eBtnEvent::L_PRESSED>, this);
            bsp_btn_register_callback(BOARD_BTN_ID_PREV, BUTTON_PRESS_UP,
                                      button_event_handler<app::eBtnEvent::L_RELEASED>, this);
            bsp_btn_register_callback(BOARD_BTN_ID_NEXT, BUTTON_PRESS_DOWN,
                                      button_event_handler<app::eBtnEvent::R_PRESSED>, this);
            bsp_btn_register_callback(BOARD_BTN_ID_NEXT, BUTTON_PRESS_UP,
                                      button_event_handler<app::eBtnEvent::R_RELEASED>, this);
            bsp_btn_register_callback(BOARD_BTN_ID_ENTER, BUTTON_SINGLE_CLICK,
                                      button_event_handler<app::eBtnEvent::M_CLICK>, this);
            bsp_btn_register_callback(BOARD_BTN_ID_ENTER, BUTTON_PRESS_REPEAT,
                                      button_event_handler<app::eBtnEvent::M_DCLICK>, this);
        }

        static AppButton &getObject(void *btn_ptr)
        {
            button_dev_t *btn_dev = reinterpret_cast<button_dev_t *>(btn_ptr);
            return *(reinterpret_cast<app::AppButton *>(btn_dev->cb_user_data));
        }

        QueueHandle_t getEventQueue(void) const { return m_event_queue; }
    };
}

namespace
{
    template <app::eBtnEvent E>
    void button_event_handler(void *btn_ptr)
    {
        app::AppButton &app_btn = app::AppButton::getObject(btn_ptr);
        app::eBtnEvent evt{E};
        xQueueSend(app_btn.getEventQueue(), (void *)(&evt), 0);
    }
}
