/*
 * SPDX-FileCopyrightText: 2015-2022 Espressif Systems (Shanghai) CO LTD
 *
 * SPDX-License-Identifier: Unlicense OR CC0-1.0
 */

#include "ui_main.h"
#include "esp_check.h"
#include "esp_log.h"
#include "lv_symbol_extra_def.h"
#include "lvgl.h"
#include "ui_about_us.h"
#include "ui_boot_animate.h"
#include "ui_matter_ctrl.h"
#include <sys/time.h>
#include "bsp/esp-bsp.h"
#include "freertos/FreeRTOS.h"
#include "freertos/semphr.h"
#include "freertos/task.h"

static const char *TAG = "ui_main";

static int g_item_index = 0;
static lv_group_t *g_btn_op_group = NULL;
static button_style_t g_btn_styles;
static lv_obj_t *g_page_menu = NULL;
bool wifi_connected = false;

/* Creates a semaphore to handle concurrent call to lvgl stuff
 * If you wish to call *any* lvgl function from other threads/tasks
 * you should lock on the very same semaphore! */
SemaphoreHandle_t g_guisemaphore;
static lv_obj_t *g_lab_wifi = NULL;
static lv_obj_t *g_status_bar = NULL;

static void ui_main_menu(int32_t index_id);
static void ui_led_set_visible(bool visible);

void ui_acquire(void)
{
    bsp_display_lock(0);
}

void ui_release(void)
{
    bsp_display_unlock();
}

static void ui_button_style_init(void)
{
    /*Init the style for the default state*/

    lv_style_init(&g_btn_styles.style);

    lv_style_set_radius(&g_btn_styles.style, 5);

    lv_style_set_bg_color(&g_btn_styles.style, lv_color_make(255, 255, 255));

    lv_style_set_border_opa(&g_btn_styles.style, LV_OPA_30);
    lv_style_set_border_width(&g_btn_styles.style, 2);
    lv_style_set_border_color(&g_btn_styles.style, lv_palette_main(LV_PALETTE_GREY));

    lv_style_set_shadow_width(&g_btn_styles.style, 7);
    lv_style_set_shadow_color(&g_btn_styles.style, lv_color_make(0, 0, 0));
    lv_style_set_shadow_ofs_x(&g_btn_styles.style, 0);
    lv_style_set_shadow_ofs_y(&g_btn_styles.style, 0);

    /*Init the pressed style*/

    lv_style_init(&g_btn_styles.style_pr);

    lv_style_set_border_opa(&g_btn_styles.style_pr, LV_OPA_40);
    lv_style_set_border_width(&g_btn_styles.style_pr, 2);
    lv_style_set_border_color(&g_btn_styles.style_pr, lv_palette_main(LV_PALETTE_GREY));

    lv_style_init(&g_btn_styles.style_focus);
    lv_style_set_outline_color(&g_btn_styles.style_focus, lv_color_make(255, 0, 0));

    lv_style_init(&g_btn_styles.style_focus_no_outline);
    lv_style_set_outline_width(&g_btn_styles.style_focus_no_outline, 0);
}

button_style_t *ui_button_styles(void)
{
    return &g_btn_styles;
}

lv_group_t *ui_get_btn_op_group(void)
{
    return g_btn_op_group;
}

static void ui_status_bar_set_visible(bool visible)
{
    if (visible) {
        // update all state
        ui_main_status_bar_set_wifi(wifi_connected);
        lv_obj_clear_flag(g_status_bar, LV_OBJ_FLAG_HIDDEN);
    } else {
        lv_obj_add_flag(g_status_bar, LV_OBJ_FLAG_HIDDEN);
    }
}

lv_obj_t *ui_main_get_status_bar(void)
{
    return g_status_bar;
}

void ui_main_status_bar_set_wifi(bool is_connected)
{
    if (g_lab_wifi) {
        lv_label_set_text_static(g_lab_wifi, is_connected ? LV_SYMBOL_WIFI : LV_SYMBOL_EXTRA_WIFI_OFF);
    }
}

static void about_us_end_cb(void)
{
    ESP_LOGI(TAG, "about_us end");
    ui_main_menu(g_item_index);
}

static void matter_ctrl_end_cb(void)
{
    ESP_LOGI(TAG, "matter_ctrl end");
    ui_main_menu(g_item_index);
}

typedef struct {
    char *name;
    void *img_src;
} item_desc_t;

LV_IMG_DECLARE(icon_matter_ctrl)
LV_IMG_DECLARE(icon_about_us)

static item_desc_t item[] = {
    {.name = "Matter Controller", .img_src = (void *)&icon_matter_ctrl},
    {.name = "About Us", .img_src = (void *)&icon_about_us},
};

static lv_obj_t *g_img_btn, *g_img_item = NULL;
static lv_obj_t *g_lab_item = NULL;
static lv_obj_t *g_led_item[2];
static size_t g_item_size = sizeof(item) / sizeof(item[0]);

static lv_obj_t *g_focus_last_obj = NULL;
static lv_obj_t *g_group_list[3] = {0};

static uint32_t menu_get_num_offset(uint32_t focus, int32_t max, int32_t offset)
{
    if (focus >= max) {
        ESP_LOGI(TAG, "[ERROR] focus should less than max");
        return focus;
    }

    uint32_t i;
    if (offset >= 0) {
        i = (focus + offset) % max;
    } else {
        offset = max + (offset % max);
        i = (focus + offset) % max;
    }
    return i;
}

static int8_t menu_direct_probe(lv_obj_t *focus_obj)
{
    int8_t direct;
    uint32_t index_max_sz, index_focus, index_prev;

    index_focus = 0;
    index_prev = 0;
    index_max_sz = sizeof(g_group_list) / sizeof(g_group_list[0]);

    for (int i = 0; i < index_max_sz; i++) {
        if (focus_obj == g_group_list[i]) {
            index_focus = i;
        }
        if (g_focus_last_obj == g_group_list[i]) {
            index_prev = i;
        }
    }

    if (NULL == g_focus_last_obj) {
        direct = 0;
    } else if (index_focus == menu_get_num_offset(index_prev, index_max_sz, 1)) {
        direct = 1;
    } else if (index_focus == menu_get_num_offset(index_prev, index_max_sz, -1)) {
        direct = -1;
    } else {
        direct = 0;
    }

    g_focus_last_obj = focus_obj;
    return direct;
}

void menu_new_item_select(lv_obj_t *obj)
{
    int8_t direct = menu_direct_probe(obj);
    g_item_index = menu_get_num_offset(g_item_index, g_item_size, direct);
    ESP_LOGI(TAG, "slected:%d, direct:%d", g_item_index, direct);

    lv_led_on(g_led_item[g_item_index]);
    lv_img_set_src(g_img_item, item[g_item_index].img_src);
    lv_label_set_text_static(g_lab_item, item[g_item_index].name);
}

static void menu_prev_cb(lv_event_t *e)
{
    lv_event_code_t code = lv_event_get_code(e);

    if (LV_EVENT_RELEASED == code) {
        lv_led_off(g_led_item[g_item_index]);
        if (0 == g_item_index) {
            g_item_index = g_item_size;
        }
        g_item_index--;
        lv_led_on(g_led_item[g_item_index]);
        lv_img_set_src(g_img_item, item[g_item_index].img_src);
        lv_label_set_text_static(g_lab_item, item[g_item_index].name);
    }
}

static void menu_next_cb(lv_event_t *e)
{
    lv_event_code_t code = lv_event_get_code(e);

    if (LV_EVENT_RELEASED == code) {
        lv_led_off(g_led_item[g_item_index]);
        g_item_index++;
        if (g_item_index >= g_item_size) {
            g_item_index = 0;
        }
        lv_led_on(g_led_item[g_item_index]);
        lv_img_set_src(g_img_item, item[g_item_index].img_src);
        lv_label_set_text_static(g_lab_item, item[g_item_index].name);
    }
}

static void menu_enter_cb(lv_event_t *e)
{
    lv_event_code_t code = lv_event_get_code(e);
    lv_obj_t *obj = lv_event_get_user_data(e);

    if (LV_EVENT_FOCUSED == code) {
        lv_led_off(g_led_item[g_item_index]);
        menu_new_item_select(obj);
    } else if (LV_EVENT_CLICKED == code) {
        lv_obj_t *menu_btn_parent = lv_obj_get_parent(obj);
        ESP_LOGI(TAG, "menu click, item index = %d", g_item_index);
        if (ui_get_btn_op_group()) {
            lv_group_remove_all_objs(ui_get_btn_op_group());
        }
        ui_led_set_visible(false);
        lv_obj_del(menu_btn_parent);
        g_focus_last_obj = NULL;

        switch (g_item_index) {
        case 0:
            ui_status_bar_set_visible(true);
            ui_matter_ctrl_start(matter_ctrl_end_cb);
            break;
        case 1:
            ui_status_bar_set_visible(true);
            ui_about_us_start(about_us_end_cb);
            break;
        default:
            break;
        }
    }
}

static void ui_main_menu(int32_t index_id)
{
    if (!g_page_menu) {
        g_page_menu = lv_obj_create(lv_scr_act());
        lv_obj_set_size(g_page_menu, lv_obj_get_width(lv_obj_get_parent(g_page_menu)),
                        lv_obj_get_height(lv_obj_get_parent(g_page_menu)) -
                            lv_obj_get_height(ui_main_get_status_bar()));
        lv_obj_set_style_border_width(g_page_menu, 0, LV_PART_MAIN);
        lv_obj_set_style_bg_color(g_page_menu, lv_obj_get_style_bg_color(lv_scr_act(), LV_STATE_DEFAULT), LV_PART_MAIN);
        lv_obj_clear_flag(g_page_menu, LV_OBJ_FLAG_SCROLLABLE);
        lv_obj_align_to(g_page_menu, ui_main_get_status_bar(), LV_ALIGN_OUT_BOTTOM_LEFT, 0, 0);
    }
    ui_status_bar_set_visible(true);

    lv_obj_t *obj = lv_obj_create(g_page_menu);
    lv_obj_set_size(obj, UI_SCALING(UI_PAGE_H_RES), UI_SCALING(174));
    lv_obj_clear_flag(obj, LV_OBJ_FLAG_SCROLLABLE);
    lv_obj_set_style_radius(obj, 15, LV_STATE_DEFAULT);
    lv_obj_set_style_border_width(obj, 0, LV_STATE_DEFAULT);
    lv_obj_set_style_shadow_width(obj, 20, LV_PART_MAIN);
    lv_obj_set_style_shadow_opa(obj, LV_OPA_30, LV_PART_MAIN);
    lv_obj_align_to(obj, ui_main_get_status_bar(), LV_ALIGN_OUT_BOTTOM_MID, 0, 0);

    g_img_btn = lv_btn_create(obj);
    lv_obj_set_size(g_img_btn, UI_SCALING(80), UI_SCALING(80));
    lv_obj_add_style(g_img_btn, &ui_button_styles()->style_pr, LV_STATE_PRESSED);
    lv_obj_add_style(g_img_btn, &ui_button_styles()->style_focus_no_outline, LV_STATE_FOCUS_KEY);
    lv_obj_add_style(g_img_btn, &ui_button_styles()->style_focus_no_outline, LV_STATE_FOCUSED);
    lv_obj_set_style_bg_color(g_img_btn, lv_color_white(), LV_PART_MAIN);
    lv_obj_set_style_shadow_color(g_img_btn, lv_color_make(0, 0, 0), LV_PART_MAIN);
    lv_obj_set_style_shadow_width(g_img_btn, 15, LV_PART_MAIN);
    lv_obj_set_style_shadow_ofs_x(g_img_btn, 0, LV_PART_MAIN);
    lv_obj_set_style_shadow_ofs_y(g_img_btn, 0, LV_PART_MAIN);
    lv_obj_set_style_shadow_opa(g_img_btn, LV_OPA_50, LV_PART_MAIN);
    lv_obj_set_style_radius(g_img_btn, UI_SCALING(40), LV_PART_MAIN);
    lv_obj_align(g_img_btn, LV_ALIGN_CENTER, 0, -20);
    lv_obj_add_event_cb(g_img_btn, menu_enter_cb, LV_EVENT_ALL, g_img_btn);

    g_img_item = lv_img_create(g_img_btn);
    lv_img_set_src(g_img_item, item[index_id].img_src);
#if CONFIG_BSP_BOARD_ESP32_S3_LCD_EV_BOARD
    lv_img_set_zoom(g_img_item, 512);
#endif
    lv_obj_center(g_img_item);

    g_lab_item = lv_label_create(obj);
    lv_label_set_text_static(g_lab_item, item[index_id].name);
    lv_obj_set_style_text_font(g_lab_item, &lv_font_montserrat_32, LV_PART_MAIN);
    lv_obj_align(g_lab_item, LV_ALIGN_BOTTOM_MID, 0, 0);

    for (size_t i = 0; i < sizeof(g_led_item) / sizeof(g_led_item[0]); i++) {
        int gap = 10;
        if (NULL == g_led_item[i]) {
            g_led_item[i] = lv_led_create(g_page_menu);
        } else {
            lv_obj_clear_flag(g_led_item[i], LV_OBJ_FLAG_HIDDEN);
        }
        lv_led_off(g_led_item[i]);
        lv_obj_set_size(g_led_item[i], UI_SCALING(5), UI_SCALING(5));
        lv_obj_align_to(g_led_item[i], g_page_menu, LV_ALIGN_BOTTOM_MID, UI_SCALING(2 * gap * i - 2 * gap + 10), 0);
    }
    lv_led_on(g_led_item[index_id]);

    lv_obj_t *btn_prev = lv_btn_create(obj);
    lv_obj_add_style(btn_prev, &ui_button_styles()->style_pr, LV_STATE_PRESSED);
    lv_obj_add_style(btn_prev, &ui_button_styles()->style_focus_no_outline, LV_STATE_FOCUS_KEY);
    lv_obj_add_style(btn_prev, &ui_button_styles()->style_focus_no_outline, LV_STATE_FOCUSED);

    lv_obj_set_size(btn_prev, UI_SCALING(40), UI_SCALING(40));
    lv_obj_set_style_bg_color(btn_prev, lv_color_white(), LV_PART_MAIN);
    lv_obj_set_style_shadow_color(btn_prev, lv_color_make(0, 0, 0), LV_PART_MAIN);
    lv_obj_set_style_shadow_width(btn_prev, 15, LV_PART_MAIN);
    lv_obj_set_style_shadow_opa(btn_prev, LV_OPA_50, LV_PART_MAIN);
    lv_obj_set_style_shadow_ofs_x(btn_prev, 0, LV_PART_MAIN);
    lv_obj_set_style_shadow_ofs_y(btn_prev, 0, LV_PART_MAIN);
    lv_obj_set_style_radius(btn_prev, UI_SCALING(20), LV_PART_MAIN);
    lv_obj_align_to(btn_prev, obj, LV_ALIGN_LEFT_MID, 0, 0);
    lv_obj_t *label = lv_label_create(btn_prev);
#if CONFIG_BSP_BOARD_ESP32_S3_LCD_EV_BOARD
    lv_obj_set_style_text_font(label, &lv_font_montserrat_32, LV_PART_MAIN);
#endif
    lv_label_set_text_static(label, LV_SYMBOL_LEFT);
    lv_obj_set_style_text_color(label, lv_color_make(5, 5, 5), LV_PART_MAIN);
    lv_obj_center(label);
    lv_obj_add_event_cb(btn_prev, menu_prev_cb, LV_EVENT_ALL, btn_prev);

    lv_obj_t *btn_next = lv_btn_create(obj);
    lv_obj_add_style(btn_next, &ui_button_styles()->style_pr, LV_STATE_PRESSED);
    lv_obj_add_style(btn_next, &ui_button_styles()->style_focus_no_outline, LV_STATE_FOCUS_KEY);
    lv_obj_add_style(btn_next, &ui_button_styles()->style_focus_no_outline, LV_STATE_FOCUSED);

    lv_obj_set_size(btn_next, UI_SCALING(40), UI_SCALING(40));
    lv_obj_set_style_bg_color(btn_next, lv_color_white(), LV_PART_MAIN);
    lv_obj_set_style_shadow_color(btn_next, lv_color_make(0, 0, 0), LV_PART_MAIN);
    lv_obj_set_style_shadow_width(btn_next, 15, LV_PART_MAIN);
    lv_obj_set_style_shadow_opa(btn_next, LV_OPA_50, LV_PART_MAIN);
    lv_obj_set_style_shadow_ofs_x(btn_next, 0, LV_PART_MAIN);
    lv_obj_set_style_shadow_ofs_y(btn_next, 0, LV_PART_MAIN);
    lv_obj_set_style_radius(btn_next, UI_SCALING(20), LV_PART_MAIN);
    lv_obj_align_to(btn_next, obj, LV_ALIGN_RIGHT_MID, 0, 0);
    label = lv_label_create(btn_next);
#if CONFIG_BSP_BOARD_ESP32_S3_LCD_EV_BOARD
    lv_obj_set_style_text_font(label, &lv_font_montserrat_32, LV_PART_MAIN);
#endif
    lv_label_set_text_static(label, LV_SYMBOL_RIGHT);
    lv_obj_set_style_text_color(label, lv_color_make(5, 5, 5), LV_PART_MAIN);
    lv_obj_center(label);
    lv_obj_add_event_cb(btn_next, menu_next_cb, LV_EVENT_ALL, btn_next);
}

static void ui_after_boot(void)
{
    ui_main_menu(g_item_index);
}

static void clock_run_cb(lv_timer_t *timer)
{
    lv_obj_t *lab_time = (lv_obj_t *)timer->user_data;
    time_t now;
    struct tm timeinfo;
    time(&now);
    localtime_r(&now, &timeinfo);
    lv_label_set_text_fmt(lab_time, "%02u:%02u", timeinfo.tm_hour, timeinfo.tm_min);
}

esp_err_t ui_main_start(void)
{
    ui_acquire();
    lv_obj_set_style_bg_color(lv_scr_act(), lv_color_make(237, 238, 239), LV_STATE_DEFAULT);
    ui_button_style_init();

    lv_indev_t *indev = lv_indev_get_next(NULL);

    if ((lv_indev_get_type(indev) == LV_INDEV_TYPE_KEYPAD) || lv_indev_get_type(indev) == LV_INDEV_TYPE_ENCODER) {
        ESP_LOGI(TAG, "Input device type is keypad");
        g_btn_op_group = lv_group_create();
        lv_indev_set_group(indev, g_btn_op_group);
    } else if (lv_indev_get_type(indev) == LV_INDEV_TYPE_BUTTON) {
        ESP_LOGI(TAG, "Input device type have button");
    } else if (lv_indev_get_type(indev) == LV_INDEV_TYPE_POINTER) {
        ESP_LOGI(TAG, "Input device type have pointer");
    }

    // Create status bar
    g_status_bar = lv_obj_create(lv_scr_act());
    lv_obj_set_size(g_status_bar, lv_obj_get_width(lv_obj_get_parent(g_status_bar)), UI_SCALING(36));
    lv_obj_clear_flag(g_status_bar, LV_OBJ_FLAG_SCROLLABLE);
    lv_obj_set_style_radius(g_status_bar, 0, LV_STATE_DEFAULT);
    lv_obj_set_style_bg_color(g_status_bar, lv_obj_get_style_bg_color(lv_scr_act(), LV_STATE_DEFAULT), LV_PART_MAIN);
    lv_obj_set_style_border_width(g_status_bar, 0, LV_PART_MAIN);
    lv_obj_set_style_shadow_width(g_status_bar, 0, LV_PART_MAIN);
    lv_obj_align(g_status_bar, LV_ALIGN_TOP_MID, 0, 0);

    lv_obj_t *lab_time = lv_label_create(g_status_bar);
    lv_label_set_text_static(lab_time, "23:59");
    lv_obj_align(lab_time, LV_ALIGN_LEFT_MID, 0, 0);
#if CONFIG_BSP_BOARD_ESP32_S3_LCD_EV_BOARD
    lv_obj_set_style_text_font(lab_time, &lv_font_montserrat_24, LV_PART_MAIN);
#endif
    lv_timer_t *timer = lv_timer_create(clock_run_cb, 1000, (void *)lab_time);
    clock_run_cb(timer);

    g_lab_wifi = lv_label_create(g_status_bar);
#if CONFIG_BSP_BOARD_ESP32_S3_LCD_EV_BOARD
    lv_obj_set_style_text_font(g_lab_wifi, &lv_font_montserrat_24, LV_PART_MAIN);
#endif
    lv_obj_align_to(g_lab_wifi, lab_time, LV_ALIGN_OUT_RIGHT_MID, UI_SCALING(10), 0);

    ui_status_bar_set_visible(0);

    boot_animate_start(ui_after_boot);

    ui_release();
    return ESP_OK;
}

/* **************** MISC FUNCTION **************** */
static void ui_led_set_visible(bool visible)
{
    for (size_t i = 0; i < sizeof(g_led_item) / sizeof(g_led_item[0]); i++) {
        if (NULL != g_led_item[i]) {
            if (visible) {
                lv_obj_clear_flag(g_led_item[i], LV_OBJ_FLAG_HIDDEN);
            } else {
                lv_obj_add_flag(g_led_item[i], LV_OBJ_FLAG_HIDDEN);
            }
        }
    }
}
