// SquareLine LVGL GENERATED FILE
// EDITOR VERSION: SquareLine Studio 1.1.1
// LVGL VERSION: 8.2.0
// PROJECT: audio_player

#include "ui.h"
#include "ui_helpers.h"

///////////////////// VARIABLES ////////////////////
lv_obj_t * ui_Screen1;
void ui_event_btnPlay(lv_event_t * e);
lv_obj_t * ui_btnPlay;
lv_obj_t * ui_txtPlayButton;
void ui_event_barVolume(lv_event_t * e);
lv_obj_t * ui_barVolume;
lv_obj_t * ui_txtFilename;
void ui_event_btnVolumeDown(lv_event_t * e);
lv_obj_t * ui_btnVolumeDown;
void ui_event_btnVolumeUp(lv_event_t * e);
lv_obj_t * ui_btnVolumeUp;
void ui_event_btnPrev(lv_event_t * e);
lv_obj_t * ui_btnPrev;
void ui_event_btnNext(lv_event_t * e);
lv_obj_t * ui_btnNext;
lv_obj_t * ui_imgAnimal;

///////////////////// TEST LVGL SETTINGS ////////////////////
#if LV_COLOR_DEPTH != 16
    #error "LV_COLOR_DEPTH should be 16bit to match SquareLine Studio's settings"
#endif
#if LV_COLOR_16_SWAP !=1
    #error "LV_COLOR_16_SWAP should be 1 to match SquareLine Studio's settings"
#endif

///////////////////// ANIMATIONS ////////////////////

///////////////////// FUNCTIONS ////////////////////
void ui_event_btnPlay(lv_event_t * e)
{
    lv_event_code_t event_code = lv_event_get_code(e);
    lv_obj_t * target = lv_event_get_target(e);
    if(event_code == LV_EVENT_CLICKED) {
        play_clicked(e);
    }
    if(event_code == LV_EVENT_FOCUSED) {
        play_focused(e);
    }
}
void ui_event_barVolume(lv_event_t * e)
{
    lv_event_code_t event_code = lv_event_get_code(e);
    lv_obj_t * target = lv_event_get_target(e);
    if(event_code == LV_EVENT_FOCUSED) {
        volume_focused(e);
    }
}
void ui_event_btnVolumeDown(lv_event_t * e)
{
    lv_event_code_t event_code = lv_event_get_code(e);
    lv_obj_t * target = lv_event_get_target(e);
    if(event_code == LV_EVENT_CLICKED) {
        vdown_clicked(e);
    }
}
void ui_event_btnVolumeUp(lv_event_t * e)
{
    lv_event_code_t event_code = lv_event_get_code(e);
    lv_obj_t * target = lv_event_get_target(e);
    if(event_code == LV_EVENT_CLICKED) {
        vup_clicked(e);
    }
}
void ui_event_btnPrev(lv_event_t * e)
{
    lv_event_code_t event_code = lv_event_get_code(e);
    lv_obj_t * target = lv_event_get_target(e);
    if(event_code == LV_EVENT_CLICKED) {
        prev_clicked(e);
    }
}
void ui_event_btnNext(lv_event_t * e)
{
    lv_event_code_t event_code = lv_event_get_code(e);
    lv_obj_t * target = lv_event_get_target(e);
    if(event_code == LV_EVENT_CLICKED) {
        next_clicked(e);
    }
}

///////////////////// SCREENS ////////////////////
void ui_Screen1_screen_init(void)
{
    ui_Screen1 = lv_obj_create(NULL);
    lv_obj_clear_flag(ui_Screen1, LV_OBJ_FLAG_SCROLLABLE);      /// Flags
    lv_obj_set_style_bg_color(ui_Screen1, lv_color_hex(0x000000), LV_PART_MAIN | LV_STATE_DEFAULT);
    lv_obj_set_style_bg_opa(ui_Screen1, 255, LV_PART_MAIN | LV_STATE_DEFAULT);

    ui_btnPlay = lv_btn_create(ui_Screen1);
    lv_obj_set_width(ui_btnPlay, 100);
    lv_obj_set_height(ui_btnPlay, 33);
    lv_obj_set_x(ui_btnPlay, -1);
    lv_obj_set_y(ui_btnPlay, 92);
    lv_obj_set_align(ui_btnPlay, LV_ALIGN_CENTER);
    lv_obj_add_flag(ui_btnPlay, LV_OBJ_FLAG_SCROLL_ON_FOCUS);     /// Flags
    lv_obj_clear_flag(ui_btnPlay, LV_OBJ_FLAG_SCROLLABLE);      /// Flags
    lv_obj_set_style_bg_color(ui_btnPlay, lv_color_hex(0x4C93F4), LV_PART_MAIN | LV_STATE_DEFAULT);
    lv_obj_set_style_bg_opa(ui_btnPlay, 255, LV_PART_MAIN | LV_STATE_DEFAULT);
    lv_obj_set_style_text_color(ui_btnPlay, lv_color_hex(0x000000), LV_PART_MAIN | LV_STATE_DEFAULT);
    lv_obj_set_style_text_opa(ui_btnPlay, 255, LV_PART_MAIN | LV_STATE_DEFAULT);
    lv_obj_set_style_text_align(ui_btnPlay, LV_TEXT_ALIGN_AUTO, LV_PART_MAIN | LV_STATE_DEFAULT);
    lv_obj_set_style_text_decor(ui_btnPlay, LV_TEXT_DECOR_NONE, LV_PART_MAIN | LV_STATE_DEFAULT);
    lv_obj_set_style_text_font(ui_btnPlay, &lv_font_montserrat_16, LV_PART_MAIN | LV_STATE_DEFAULT);

    ui_txtPlayButton = lv_label_create(ui_btnPlay);
    lv_obj_set_width(ui_txtPlayButton, LV_SIZE_CONTENT);   /// 1
    lv_obj_set_height(ui_txtPlayButton, LV_SIZE_CONTENT);    /// 1
    lv_obj_set_x(ui_txtPlayButton, 0);
    lv_obj_set_y(ui_txtPlayButton, 1);
    lv_obj_set_align(ui_txtPlayButton, LV_ALIGN_CENTER);
    lv_label_set_text(ui_txtPlayButton, "Play");

    ui_barVolume = lv_bar_create(ui_Screen1);
    lv_bar_set_value(ui_barVolume, 25, LV_ANIM_OFF);
    lv_obj_set_width(ui_barVolume, 178);
    lv_obj_set_height(ui_barVolume, 10);
    lv_obj_set_x(ui_barVolume, -2);
    lv_obj_set_y(ui_barVolume, 25);
    lv_obj_set_align(ui_barVolume, LV_ALIGN_TOP_MID);

    lv_obj_set_style_bg_color(ui_barVolume, lv_color_hex(0x4C93F4), LV_PART_INDICATOR | LV_STATE_DEFAULT);
    lv_obj_set_style_bg_opa(ui_barVolume, 255, LV_PART_INDICATOR | LV_STATE_DEFAULT);

    ui_txtFilename = lv_label_create(ui_Screen1);
    lv_obj_set_width(ui_txtFilename, LV_SIZE_CONTENT);   /// 1
    lv_obj_set_height(ui_txtFilename, LV_SIZE_CONTENT);    /// 1
    lv_obj_set_x(ui_txtFilename, 69);
    lv_obj_set_y(ui_txtFilename, 1);
    lv_obj_set_align(ui_txtFilename, LV_ALIGN_CENTER);
    lv_label_set_text(ui_txtFilename, "filename");
    lv_obj_set_style_text_color(ui_txtFilename, lv_color_hex(0xFFFFFF), LV_PART_MAIN | LV_STATE_DEFAULT);
    lv_obj_set_style_text_opa(ui_txtFilename, 255, LV_PART_MAIN | LV_STATE_DEFAULT);
    lv_obj_set_style_text_font(ui_txtFilename, &lv_font_montserrat_24, LV_PART_MAIN | LV_STATE_DEFAULT);

    ui_btnVolumeDown = lv_imgbtn_create(ui_Screen1);
    lv_imgbtn_set_src(ui_btnVolumeDown, LV_IMGBTN_STATE_RELEASED, NULL, &ui_img_1552218578, NULL);
    lv_imgbtn_set_src(ui_btnVolumeDown, LV_IMGBTN_STATE_PRESSED, NULL, &ui_img_1552235971, NULL);
    lv_obj_set_width(ui_btnVolumeDown, 36);
    lv_obj_set_height(ui_btnVolumeDown, 36);
    lv_obj_set_x(ui_btnVolumeDown, -129);
    lv_obj_set_y(ui_btnVolumeDown, -90);
    lv_obj_set_align(ui_btnVolumeDown, LV_ALIGN_CENTER);
    lv_obj_set_style_radius(ui_btnVolumeDown, 18, LV_PART_MAIN | LV_STATE_DEFAULT);
    lv_obj_set_style_bg_color(ui_btnVolumeDown, lv_color_hex(0xFFFFFF), LV_PART_MAIN | LV_STATE_DEFAULT);
    lv_obj_set_style_bg_opa(ui_btnVolumeDown, 255, LV_PART_MAIN | LV_STATE_DEFAULT);

    ui_btnVolumeUp = lv_imgbtn_create(ui_Screen1);
    lv_imgbtn_set_src(ui_btnVolumeUp, LV_IMGBTN_STATE_RELEASED, NULL, &ui_img_1258062811, NULL);
    lv_imgbtn_set_src(ui_btnVolumeUp, LV_IMGBTN_STATE_PRESSED, NULL, &ui_img_1258080204, NULL);
    lv_obj_set_width(ui_btnVolumeUp, 36);
    lv_obj_set_height(ui_btnVolumeUp, 36);
    lv_obj_set_x(ui_btnVolumeUp, 125);
    lv_obj_set_y(ui_btnVolumeUp, -90);
    lv_obj_set_align(ui_btnVolumeUp, LV_ALIGN_CENTER);
    lv_obj_set_style_radius(ui_btnVolumeUp, 18, LV_PART_MAIN | LV_STATE_DEFAULT);
    lv_obj_set_style_bg_color(ui_btnVolumeUp, lv_color_hex(0xFFFFFF), LV_PART_MAIN | LV_STATE_DEFAULT);
    lv_obj_set_style_bg_opa(ui_btnVolumeUp, 255, LV_PART_MAIN | LV_STATE_DEFAULT);

    ui_btnPrev = lv_imgbtn_create(ui_Screen1);
    lv_imgbtn_set_src(ui_btnPrev, LV_IMGBTN_STATE_RELEASED, NULL, &ui_img_603081905, NULL);
    lv_imgbtn_set_src(ui_btnPrev, LV_IMGBTN_STATE_PRESSED, NULL, &ui_img_603097248, NULL);
    lv_obj_set_width(ui_btnPrev, 36);
    lv_obj_set_height(ui_btnPrev, 36);
    lv_obj_set_x(ui_btnPrev, -99);
    lv_obj_set_y(ui_btnPrev, 94);
    lv_obj_set_align(ui_btnPrev, LV_ALIGN_CENTER);
    lv_obj_set_style_bg_color(ui_btnPrev, lv_color_hex(0xFFFFFF), LV_PART_MAIN | LV_STATE_DEFAULT);
    lv_obj_set_style_bg_opa(ui_btnPrev, 255, LV_PART_MAIN | LV_STATE_DEFAULT);

    ui_btnNext = lv_imgbtn_create(ui_Screen1);
    lv_imgbtn_set_src(ui_btnNext, LV_IMGBTN_STATE_RELEASED, NULL, &ui_img_1310788941, NULL);
    lv_imgbtn_set_src(ui_btnNext, LV_IMGBTN_STATE_PRESSED, NULL, &ui_img_1310804284, NULL);
    lv_obj_set_width(ui_btnNext, 36);
    lv_obj_set_height(ui_btnNext, 36);
    lv_obj_set_x(ui_btnNext, 94);
    lv_obj_set_y(ui_btnNext, 94);
    lv_obj_set_align(ui_btnNext, LV_ALIGN_CENTER);
    lv_obj_set_style_bg_color(ui_btnNext, lv_color_hex(0xFFFFFF), LV_PART_MAIN | LV_STATE_DEFAULT);
    lv_obj_set_style_bg_opa(ui_btnNext, 255, LV_PART_MAIN | LV_STATE_DEFAULT);

    ui_imgAnimal = lv_img_create(ui_Screen1);
    lv_obj_set_width(ui_imgAnimal, 128);
    lv_obj_set_height(ui_imgAnimal, 128);
    lv_obj_set_x(ui_imgAnimal, -65);
    lv_obj_set_y(ui_imgAnimal, 0);
    lv_obj_set_align(ui_imgAnimal, LV_ALIGN_CENTER);
    lv_obj_add_flag(ui_imgAnimal, LV_OBJ_FLAG_ADV_HITTEST);     /// Flags
    lv_obj_clear_flag(ui_imgAnimal, LV_OBJ_FLAG_SCROLLABLE);      /// Flags

    lv_obj_add_event_cb(ui_btnPlay, ui_event_btnPlay, LV_EVENT_ALL, NULL);
    lv_obj_add_event_cb(ui_barVolume, ui_event_barVolume, LV_EVENT_ALL, NULL);
    lv_obj_add_event_cb(ui_btnVolumeDown, ui_event_btnVolumeDown, LV_EVENT_ALL, NULL);
    lv_obj_add_event_cb(ui_btnVolumeUp, ui_event_btnVolumeUp, LV_EVENT_ALL, NULL);
    lv_obj_add_event_cb(ui_btnPrev, ui_event_btnPrev, LV_EVENT_ALL, NULL);
    lv_obj_add_event_cb(ui_btnNext, ui_event_btnNext, LV_EVENT_ALL, NULL);

}

void ui_init(void)
{
    lv_disp_t * dispp = lv_disp_get_default();
    lv_theme_t * theme = lv_theme_default_init(dispp, lv_palette_main(LV_PALETTE_BLUE), lv_palette_main(LV_PALETTE_RED),
                                               false, LV_FONT_DEFAULT);
    lv_disp_set_theme(dispp, theme);
    ui_Screen1_screen_init();
    lv_disp_load_scr(ui_Screen1);
}
