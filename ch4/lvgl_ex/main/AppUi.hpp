#pragma once

#include <mutex>
#include <vector>

#include "bsp_lcd.h"
#include "esp_log.h"
#include "freertos/FreeRTOS.h"
#include "freertos/task.h"
#include "lvgl/lvgl.h"
#include "lv_port/lv_port.h"
#include "ui.h"
#include "AppButton.hpp"

namespace app
{
    class AppUi
    {
    private:
        constexpr static const char *TAG{"gui"};

        static std::mutex m_ui_access;
        static void lvglTask(void *param)
        {
            while (true)
            {
                {
                    std::lock_guard<std::mutex> lock(m_ui_access);
                    lv_task_handler();
                }
                vTaskDelay(pdMS_TO_TICKS(10));
            }
        }

        std::vector<lv_obj_t *> m_screens;
        int m_scr_pos;

    public:
        void init(void)
        {
            lv_port_init();
            ui_init();
            m_scr_pos = 0;
            m_screens.push_back(ui_Screen1);
            m_screens.push_back(ui_Screen2);
            m_screens.push_back(ui_Screen3);
            m_screens.push_back(ui_Screen4);
            xTaskCreatePinnedToCore(lvglTask, "lvgl", 6 * 1024, nullptr, 3, nullptr, 0);

            bsp_lcd_set_backlight(true);
        }

        void buttonEventHandler(sAppButtonEvent &btn_evt)
        {
            std::lock_guard<std::mutex> lock(m_ui_access);
            switch (btn_evt.btn_id)
            {
            case board_btn_id_t::BOARD_BTN_ID_PREV:
                m_scr_pos = (m_scr_pos - 1) % m_screens.size();
                lv_scr_load(m_screens[m_scr_pos]);
                break;

            case board_btn_id_t::BOARD_BTN_ID_NEXT:
                m_scr_pos = (m_scr_pos + 1) % m_screens.size();
                lv_scr_load(m_screens[m_scr_pos]);
                break;

            case board_btn_id_t::BOARD_BTN_ID_ENTER:
            {
                switch (m_scr_pos)
                {
                case 0:
                    updateTextArea(btn_evt.evt_id);
                    break;
                case 1:
                    updateLvButtonState(btn_evt.evt_id);
                    break;
                case 2:
                    toggleSwitch(btn_evt.evt_id);
                    break;
                case 3:
                    toggleSpinnerVisibility(btn_evt.evt_id);
                    break;
                default:
                    break;
                }
            }
            break;

            default:
                break;
            }
        }

        void updateTextArea(button_event_t btn_evt_id)
        {
            if (btn_evt_id == button_event_t::BUTTON_PRESS_DOWN)
            {
                lv_textarea_add_text(ui_Screen1_TextArea1, "button down\n");
            }
            else
            {
                lv_textarea_add_text(ui_Screen1_TextArea1, "button up\n");
            }
        }

        void updateLvButtonState(button_event_t btn_evt_id)
        {
            if (btn_evt_id == button_event_t::BUTTON_PRESS_DOWN)
            {
                lv_event_send(ui_Screen2_Button1, LV_EVENT_PRESSED, nullptr);
            }
            else
            {
                lv_event_send(ui_Screen2_Button1, LV_EVENT_RELEASED, nullptr);
            }
        }

        void toggleSwitch(button_event_t btn_evt_id)
        {
            static bool checked{false};
            if (btn_evt_id == button_event_t::BUTTON_PRESS_UP)
            {
                checked = !checked;
                if (checked)
                {
                    lv_obj_add_state(ui_Screen3_Switch1, LV_STATE_CHECKED);
                }
                else
                {
                    lv_obj_clear_state(ui_Screen3_Switch1, LV_STATE_CHECKED);
                }
            }
        }

        void toggleSpinnerVisibility(button_event_t btn_evt_id)
        {
            static bool hidden{false};
            if (btn_evt_id == button_event_t::BUTTON_PRESS_UP)
            {
                hidden = !hidden;
                if (hidden)
                {
                    lv_obj_add_flag(ui_Screen4_Spinner1, LV_OBJ_FLAG_HIDDEN);
                }
                else
                {
                    lv_obj_clear_flag(ui_Screen4_Spinner1, LV_OBJ_FLAG_HIDDEN);
                }
            }
        }
    };

    std::mutex AppUi::m_ui_access;
}