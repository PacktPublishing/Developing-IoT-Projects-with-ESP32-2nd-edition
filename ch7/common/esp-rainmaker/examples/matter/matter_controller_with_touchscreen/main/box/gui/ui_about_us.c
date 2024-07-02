/*
 * SPDX-FileCopyrightText: 2015-2022 Espressif Systems (Shanghai) CO LTD
 *
 * SPDX-License-Identifier: Unlicense OR CC0-1.0
 */

#include "esp_log.h"
#include "bsp/esp-bsp.h"
#include "lvgl.h"
#include "ui_main.h"
#include "ui_about_us.h"
#include "app_matter_ctrl.h"

static const char * boards_info = {
#if CONFIG_BSP_BOARD_ESP32_S3_BOX_3
    "S3_BOX_3"
#elif CONFIG_BSP_BOARD_ESP32_S3_BOX
    "S3_BOX"
#elif CONFIG_BSP_BOARD_ESP32_S3_BOX_Lite
    "S3_BOX_LITE"
#else
    "S3_LCD_EV_BOARD"
#endif
};

static void (*g_about_us_end_cb)(void) = NULL;

static void ui_about_us_page_return_click_cb(lv_event_t *e)
{
    lv_obj_t *obj = lv_event_get_user_data(e);
    if (ui_get_btn_op_group()) {
        lv_group_remove_all_objs(ui_get_btn_op_group());
    }

    lv_obj_del(obj);
    // bsp_btn_rm_all_callback(BSP_BUTTON_MAIN);
    if (g_about_us_end_cb) {
        g_about_us_end_cb();
    }
}

void ui_about_us_start(void (*fn)(void))
{
    g_about_us_end_cb = fn;

    lv_obj_t *page = lv_obj_create(lv_scr_act());
    lv_obj_set_size(page, UI_SCALING(UI_PAGE_H_RES), UI_SCALING(174));
    lv_obj_clear_flag(page, LV_OBJ_FLAG_SCROLLABLE);
    lv_obj_set_style_radius(page, 15, LV_STATE_DEFAULT);
    lv_obj_set_style_border_width(page, 0, LV_STATE_DEFAULT);
    lv_obj_set_style_shadow_width(page, 20, LV_PART_MAIN);
    lv_obj_set_style_shadow_opa(page, LV_OPA_30, LV_PART_MAIN);
    lv_obj_align_to(page, ui_main_get_status_bar(), LV_ALIGN_OUT_BOTTOM_MID, 0, 0);

    lv_obj_t *btn_return = lv_btn_create(page);
    lv_obj_set_size(btn_return, UI_SCALING(24), UI_SCALING(24));
    lv_obj_add_style(btn_return, &ui_button_styles()->style, 0);
    lv_obj_add_style(btn_return, &ui_button_styles()->style_pr, LV_STATE_PRESSED);
    lv_obj_add_style(btn_return, &ui_button_styles()->style_focus, LV_STATE_FOCUS_KEY);
    lv_obj_add_style(btn_return, &ui_button_styles()->style_focus, LV_STATE_FOCUSED);
    lv_obj_align(btn_return, LV_ALIGN_TOP_LEFT, 0, 0);
    lv_obj_t *lab_btn_text = lv_label_create(btn_return);
#if CONFIG_BSP_BOARD_ESP32_S3_LCD_EV_BOARD
    lv_obj_set_style_text_font(lab_btn_text, &lv_font_montserrat_24, LV_PART_MAIN);
#endif
    lv_label_set_text_static(lab_btn_text, LV_SYMBOL_LEFT);
    lv_obj_set_style_text_color(lab_btn_text, lv_color_make(158, 158, 158), LV_STATE_DEFAULT);
    lv_obj_center(lab_btn_text);
    lv_obj_add_event_cb(btn_return, ui_about_us_page_return_click_cb, LV_EVENT_CLICKED, page);

    if (ui_get_btn_op_group()) {
        lv_group_add_obj(ui_get_btn_op_group(), btn_return);
    }

    lv_obj_t *img = lv_img_create(page);
    lv_obj_align(img, LV_ALIGN_TOP_MID, 0, UI_SCALING(20));
    LV_IMG_DECLARE(icon_box);
    lv_img_set_src(img, &icon_box);

#if CONFIG_BSP_BOARD_ESP32_S3_LCD_EV_BOARD
    lv_img_set_zoom(img, 512);
#endif

    char msg[256] = {0};
    snprintf(msg, sizeof(msg),
             "#000000 Software Ver: # "  "#888888 V%u.%u.%u#\n"
             "#000000 ESP-IDF Ver: # "   "#888888 %s#\n"
             "#000000 Board: # "         "#888888 %s#",
             BOX_DEMO_VERSION_MAJOR, BOX_DEMO_VERSION_MINOR, BOX_DEMO_VERSION_PATCH,
             esp_get_idf_version(),
             boards_info);

    lv_obj_t *lab = lv_label_create(page);
    lv_label_set_recolor(lab, true);
    lv_label_set_text(lab, msg);
    lv_obj_align(lab, LV_ALIGN_BOTTOM_LEFT, 0, -10);
}
