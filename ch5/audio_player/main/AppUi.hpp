#pragma once

#include <mutex>
#include <vector>
#include <cstdio>

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

        enum class eActivePanel
        {
            VolumeControl,
            Playlist
        };

        eActivePanel m_active_panel;

        int m_player_index;
        lv_fs_drv_t m_drv;

    public:

        void init(void)
        {
            m_active_panel = eActivePanel::Playlist;

            lv_port_init();
            ui_init();

            lv_event_send(ui_btnPlay, LV_EVENT_FOCUSED, nullptr);
            lv_img_set_src(ui_imgAnimal, "S:/spiffs/dog.png");
            

            xTaskCreatePinnedToCore(lvglTask, "lvgl", 6 * 1024, nullptr, 3, nullptr, 0);

            bsp_lcd_set_backlight(true);
        }

        void buttonEventHandler(sAppButtonEvent &btn_evt)
        {
            std::lock_guard<std::mutex> lock(m_ui_access);
            switch (btn_evt.btn_id)
            {
            case board_btn_id_t::BOARD_BTN_ID_PREV:
                if (m_active_panel == eActivePanel::Playlist)
                {
                }
                else
                {
                }
                break;

            case board_btn_id_t::BOARD_BTN_ID_NEXT:
                if (m_active_panel == eActivePanel::Playlist)
                {
                }
                else
                {
                }
                break;

            case board_btn_id_t::BOARD_BTN_ID_ENTER:
                if (m_active_panel == eActivePanel::Playlist)
                {
                    if (btn_evt.evt_id == button_event_t::BUTTON_PRESS_REPEAT)
                    {
                        m_active_panel = eActivePanel::VolumeControl;
                        lv_event_send(ui_barVolume, LV_EVENT_FOCUSED, nullptr);
                        // lv_obj_clear_state(ui_btnPlay, LV_STATE_FOCUSED);
                        // lv_obj_add_state(ui_barVolume, LV_STATE_FOCUSED);
                        ESP_LOGI("ui", "settin focus on bar");
                    }
                    else
                    {
                    }
                }
                else
                {
                    if (btn_evt.evt_id == button_event_t::BUTTON_PRESS_REPEAT)
                    {
                        m_active_panel = eActivePanel::Playlist;
                        lv_event_send(ui_btnPlay, LV_EVENT_FOCUSED, nullptr);
                        // lv_obj_clear_state(ui_barVolume, LV_STATE_FOCUSED);
                        // lv_obj_add_state(ui_btnPlay, LV_STATE_FOCUSED);
                        ESP_LOGI("ui", "settin focus on btn");
                    }
                    else
                    {
                    }
                }
                break;

            default:
                break;
            }
        }

        // void updateLvButtonState(button_event_t btn_evt_id)
        // {
        //     if (btn_evt_id == button_event_t::BUTTON_PRESS_DOWN)
        //     {
        //         lv_event_send(ui_Screen2_Button1, LV_EVENT_PRESSED, nullptr);
        //     }
        //     else
        //     {
        //         lv_event_send(ui_Screen2_Button1, LV_EVENT_RELEASED, nullptr);
        //     }
        // }
    };

    std::mutex AppUi::m_ui_access;
}