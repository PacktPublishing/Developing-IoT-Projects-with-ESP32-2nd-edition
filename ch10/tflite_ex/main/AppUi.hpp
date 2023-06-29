#pragma once

#include <mutex>
#include <vector>

#include "freertos/FreeRTOS.h"
#include "freertos/task.h"
#include "freertos/queue.h"
#include "esp_log.h"

#include "bsp_board.h"
#include "bsp_lcd.h"
#include "lvgl/lvgl.h"
#include "lv_port/lv_port.h"
#include "ui.h"

namespace app
{
    class AppUi
    {
    private:
        std::mutex m_ui_access;
        static void lvglTask(void *arg);

    public:
        void init(void)
        {
            bsp_board_init();
            lv_port_init();
            ui_init();
            xTaskCreate(lvglTask, "lvgl", 6 * 1024, this, 3, nullptr);

            bsp_lcd_set_backlight(true);
        }

        void drawSinePoint(float x_val, float y_val)
        {
            std::lock_guard<std::mutex> lock(m_ui_access);

            lv_coord_t x_coord = static_cast<lv_coord_t>(x_val * 30) + 50;
            lv_coord_t y_coord = static_cast<lv_coord_t>(y_val * -50) + 100;
            ESP_LOGI("lvgl", "x=%.5f y=%.5f (%d,%d)", x_val, y_val, x_coord, y_coord);
            ui_setPoint(x_coord, y_coord);
        }
    };

    void AppUi::lvglTask(void *arg)
    {
        AppUi *obj = reinterpret_cast<AppUi *>(arg);

        while (true)
        {
            {
                std::lock_guard<std::mutex> lock(obj->m_ui_access);
                lv_task_handler();
            }
            vTaskDelay(pdMS_TO_TICKS(10));
        }
    }
}