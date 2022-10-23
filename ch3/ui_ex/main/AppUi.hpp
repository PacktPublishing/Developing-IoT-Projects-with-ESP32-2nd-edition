#pragma once

#include <mutex>

#include "bsp_lcd.h"
#include "freertos/FreeRTOS.h"
#include "freertos/task.h"
#include "lvgl/lvgl.h"
#include "lv_port/lv_port.h"

namespace app
{
    class AppUi
    {
    public:
        void init(void)
        {
            lv_port_init();

            m_label_title = lv_label_create(lv_scr_act());
            lv_obj_set_style_text_color(m_label_title, lv_color_make(0, 0, 0), LV_STATE_DEFAULT);
            lv_obj_set_style_text_font(m_label_title, &lv_font_montserrat_24, LV_STATE_DEFAULT);
            lv_label_set_text(m_label_title, "Press a button");
            lv_obj_align(m_label_title, LV_ALIGN_TOP_MID, 0, 100);

            xTaskCreatePinnedToCore(lvgl_task, "lvgl", 6 * 1024, nullptr, configMAX_PRIORITIES - 3, nullptr, 0);
         
            bsp_lcd_set_backlight(true);
        }

        void setLabelText(const char *lbl_txt)
        {
            std::lock_guard<std::mutex> lock(m_ui_access);
            lv_label_set_text(m_label_title, lbl_txt);
        }

    private:
        static std::mutex m_ui_access;
        lv_obj_t *m_label_title;

        static void lvgl_task(void *param)
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
    };

    std::mutex AppUi::m_ui_access;
}