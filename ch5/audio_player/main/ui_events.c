// SquareLine LVGL GENERATED FILE
// EDITOR VERSION: SquareLine Studio 1.1.1
// LVGL VERSION: 8.2.0
// PROJECT: audio_player

#include "ui.h"
#include "esp_log.h"

void play_clicked(lv_event_t * e)
{
	// Your code here
}

void vdown_clicked(lv_event_t * e)
{
	// Your code here
}

void vup_clicked(lv_event_t * e)
{
	// Your code here
}

void prev_clicked(lv_event_t * e)
{
	// Your code here
}

void next_clicked(lv_event_t * e)
{
	// Your code here
}

#define NORMAL_COLOR 0x4C93F4
#define FOCUSED_COLOR 0xFF0000

void play_focused(lv_event_t * e)
{
    lv_obj_set_style_bg_color(ui_barVolume, lv_color_hex(NORMAL_COLOR), LV_PART_INDICATOR | LV_STATE_DEFAULT);
    lv_obj_set_style_bg_color(ui_btnPlay, lv_color_hex(FOCUSED_COLOR), LV_PART_MAIN | LV_STATE_DEFAULT);
}

void volume_focused(lv_event_t * e)
{
    lv_obj_set_style_bg_color(ui_btnPlay, lv_color_hex(NORMAL_COLOR), LV_PART_MAIN | LV_STATE_DEFAULT);
    lv_obj_set_style_bg_color(ui_barVolume, lv_color_hex(FOCUSED_COLOR), LV_PART_INDICATOR | LV_STATE_DEFAULT);
}
