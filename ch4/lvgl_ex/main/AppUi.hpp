#pragma once

#include <mutex>

#include "bsp_lcd.h"
#include "esp_log.h"
#include "freertos/FreeRTOS.h"
#include "freertos/task.h"
#include "lvgl/lvgl.h"
#include "lv_port/lv_port.h"
#include "ui.h"

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

    public:
        void init(void)
        {
            lv_port_init();

            ui_init();

            xTaskCreatePinnedToCore(lvglTask, "lvgl", 6 * 1024, nullptr, 3, nullptr, 0);

            bsp_lcd_set_backlight(true);
        }

        void buttonLeftClick(void *param)
        {
            std::lock_guard<std::mutex> lock(m_ui_access);

            if (lv_scr_act() == ui_Screen1)
            {
                
            }
            else if (lv_scr_act() == ui_Screen2)
            {
                ESP_LOGI(TAG, "left click on scr2");
            }
        }

        void buttonMiddleClick(void *param)
        {
            std::lock_guard<std::mutex> lock(m_ui_access);
        }

        void buttonRightClick(void *param)
        {
            std::lock_guard<std::mutex> lock(m_ui_access);
            if (lv_scr_act() == ui_Screen1)
            {
                ESP_LOGI(TAG, "right click on scr1");
                ESP_LOGI(TAG, "left click on scr1");
                lv_event_send(ui_scr1btn1, lv_event_code_t::LV_EVENT_CLICKED, param);
            }
            else if (lv_scr_act() == ui_Screen2)
            {
                ESP_LOGI(TAG, "right click on scr2");
            }
        }
    };

    std::mutex AppUi::m_ui_access;
}