#pragma once

#include <sys/time.h>
#include <mutex>

#include "freertos/FreeRTOS.h"
#include "freertos/task.h"
#include "freertos/semphr.h"
#include "lvgl/lvgl.h"
#include "lv_port/lv_port.h"

namespace
{
}

namespace app
{
    class AppUi
    {
    public:
        void init(void)
        {
            ESP_ERROR_CHECK(lv_port_init());

            m_label_title = lv_label_create(lv_scr_act());
            lv_obj_set_style_text_color(m_label_title, lv_color_make(0, 0, 0), LV_STATE_DEFAULT);
            lv_obj_set_style_text_font(m_label_title, &lv_font_montserrat_24, LV_STATE_DEFAULT);
            lv_label_set_text(m_label_title, "Press a button");
            lv_obj_align(m_label_title, LV_ALIGN_TOP_MID, 0, 100);

            BaseType_t ret_val = xTaskCreatePinnedToCore(lvgl_task, "lvgl", 6 * 1024, nullptr, configMAX_PRIORITIES - 3, nullptr, 0);
            ESP_ERROR_CHECK((pdPASS == ret_val) ? ESP_OK : ESP_FAIL);
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
            vTaskDelete(NULL);
        }
    };

    std::mutex AppUi::m_ui_access;
}