#pragma once

#include <mutex>

#include "bsp_board.h"
#include "freertos/FreeRTOS.h"
#include "freertos/task.h"
#include "lvgl.h"

namespace app
{
    class AppUi
    {
    private:
        lv_obj_t *m_label_title;

        static std::mutex m_ui_access;

    public:
        void init(void)
        {
            m_label_title = lv_label_create(lv_scr_act());
            lv_obj_set_style_text_color(m_label_title, lv_color_make(0, 0, 0), LV_STATE_DEFAULT);
            lv_obj_set_style_text_font(m_label_title, &lv_font_montserrat_24, LV_STATE_DEFAULT);
            lv_label_set_text(m_label_title, "Press a button");
            lv_obj_align(m_label_title, LV_ALIGN_CENTER, 0, 0);
        }

        void setLabelText(const char *lbl_txt)
        {
            std::lock_guard<std::mutex> lock(m_ui_access);
            lv_label_set_text(m_label_title, lbl_txt);
        }
    };

    std::mutex AppUi::m_ui_access;
}