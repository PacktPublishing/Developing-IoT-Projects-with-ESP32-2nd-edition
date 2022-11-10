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

        void buttonEventHandler(void *param)
        {
            std::lock_guard<std::mutex> lock(m_ui_access);
            app::sAppButtonEvent &btn_evt = *(reinterpret_cast<app::sAppButtonEvent *>(param));
            switch (btn_evt.btn_id)
            {
            case board_btn_id_t::BOARD_BTN_ID_PREV:
            {
                m_scr_pos = (m_scr_pos - 1) % m_screens.size();
                lv_scr_load(m_screens[m_scr_pos]);
            }
            break;

            case board_btn_id_t::BOARD_BTN_ID_NEXT:
            {
                m_scr_pos = (m_scr_pos + 1) % m_screens.size();
                lv_scr_load(m_screens[m_scr_pos]);
            }
            break;

            default:
                break;
            }
        }
    };

    std::mutex AppUi::m_ui_access;
}