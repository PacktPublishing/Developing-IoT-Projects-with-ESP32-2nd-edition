// SquareLine LVGL GENERATED FILE
// EDITOR VERSION: SquareLine Studio 1.1.1
// LVGL VERSION: 8.2.0
// PROJECT: lvgl_ex

#include "ui.h"
#include "ui_helpers.h"

///////////////////// VARIABLES ////////////////////
lv_obj_t * ui_Screen1;
lv_obj_t * ui_Screen1_Label1;
lv_obj_t * ui_Screen1_TextArea1;
lv_obj_t * ui_Screen2;
lv_obj_t * ui_Screen1_Label2;
lv_obj_t * ui_Screen2_Button1;
lv_obj_t * ui_Screen3;
lv_obj_t * ui_Screen1_Label3;
lv_obj_t * ui_Screen3_Switch1;
lv_obj_t * ui_Screen4;
lv_obj_t * ui_Screen1_Label4;
lv_obj_t * ui_Screen4_Spinner1;

///////////////////// TEST LVGL SETTINGS ////////////////////
#if LV_COLOR_DEPTH != 16
    #error "LV_COLOR_DEPTH should be 16bit to match SquareLine Studio's settings"
#endif
#if LV_COLOR_16_SWAP !=1
    #error "LV_COLOR_16_SWAP should be 1 to match SquareLine Studio's settings"
#endif

///////////////////// ANIMATIONS ////////////////////

///////////////////// FUNCTIONS ////////////////////

///////////////////// SCREENS ////////////////////
void ui_Screen1_screen_init(void)
{
    ui_Screen1 = lv_obj_create(NULL);
    lv_obj_clear_flag(ui_Screen1, LV_OBJ_FLAG_SCROLLABLE);      /// Flags

    ui_Screen1_Label1 = lv_label_create(ui_Screen1);
    lv_obj_set_width(ui_Screen1_Label1, LV_SIZE_CONTENT);   /// 1
    lv_obj_set_height(ui_Screen1_Label1, LV_SIZE_CONTENT);    /// 1
    lv_obj_set_x(ui_Screen1_Label1, 2);
    lv_obj_set_y(ui_Screen1_Label1, -98);
    lv_obj_set_align(ui_Screen1_Label1, LV_ALIGN_CENTER);
    lv_label_set_text(ui_Screen1_Label1, "Text area");
    lv_obj_set_style_text_font(ui_Screen1_Label1, &lv_font_montserrat_24, LV_PART_MAIN | LV_STATE_DEFAULT);

    ui_Screen1_TextArea1 = lv_textarea_create(ui_Screen1);
    lv_obj_set_width(ui_Screen1_TextArea1, 297);
    lv_obj_set_height(ui_Screen1_TextArea1, 190);
    lv_obj_set_x(ui_Screen1_TextArea1, -1);
    lv_obj_set_y(ui_Screen1_TextArea1, 17);
    lv_obj_set_align(ui_Screen1_TextArea1, LV_ALIGN_CENTER);
    lv_textarea_set_placeholder_text(ui_Screen1_TextArea1, "Placeholder...");

}
void ui_Screen2_screen_init(void)
{
    ui_Screen2 = lv_obj_create(NULL);
    lv_obj_clear_flag(ui_Screen2, LV_OBJ_FLAG_SCROLLABLE);      /// Flags

    ui_Screen1_Label2 = lv_label_create(ui_Screen2);
    lv_obj_set_width(ui_Screen1_Label2, LV_SIZE_CONTENT);   /// 1
    lv_obj_set_height(ui_Screen1_Label2, LV_SIZE_CONTENT);    /// 1
    lv_obj_set_x(ui_Screen1_Label2, 2);
    lv_obj_set_y(ui_Screen1_Label2, -98);
    lv_obj_set_align(ui_Screen1_Label2, LV_ALIGN_CENTER);
    lv_label_set_text(ui_Screen1_Label2, "Button");
    lv_obj_set_style_text_font(ui_Screen1_Label2, &lv_font_montserrat_24, LV_PART_MAIN | LV_STATE_DEFAULT);

    ui_Screen2_Button1 = lv_btn_create(ui_Screen2);
    lv_obj_set_width(ui_Screen2_Button1, 164);
    lv_obj_set_height(ui_Screen2_Button1, 86);
    lv_obj_set_x(ui_Screen2_Button1, 5);
    lv_obj_set_y(ui_Screen2_Button1, 0);
    lv_obj_set_align(ui_Screen2_Button1, LV_ALIGN_CENTER);
    lv_obj_add_flag(ui_Screen2_Button1, LV_OBJ_FLAG_SCROLL_ON_FOCUS);     /// Flags
    lv_obj_clear_flag(ui_Screen2_Button1, LV_OBJ_FLAG_SCROLLABLE);      /// Flags

}
void ui_Screen3_screen_init(void)
{
    ui_Screen3 = lv_obj_create(NULL);
    lv_obj_clear_flag(ui_Screen3, LV_OBJ_FLAG_SCROLLABLE);      /// Flags

    ui_Screen1_Label3 = lv_label_create(ui_Screen3);
    lv_obj_set_width(ui_Screen1_Label3, LV_SIZE_CONTENT);   /// 1
    lv_obj_set_height(ui_Screen1_Label3, LV_SIZE_CONTENT);    /// 1
    lv_obj_set_x(ui_Screen1_Label3, 2);
    lv_obj_set_y(ui_Screen1_Label3, -98);
    lv_obj_set_align(ui_Screen1_Label3, LV_ALIGN_CENTER);
    lv_label_set_text(ui_Screen1_Label3, "Switch");
    lv_obj_set_style_text_font(ui_Screen1_Label3, &lv_font_montserrat_24, LV_PART_MAIN | LV_STATE_DEFAULT);

    ui_Screen3_Switch1 = lv_switch_create(ui_Screen3);
    lv_obj_set_width(ui_Screen3_Switch1, 126);
    lv_obj_set_height(ui_Screen3_Switch1, 66);
    lv_obj_set_x(ui_Screen3_Switch1, 8);
    lv_obj_set_y(ui_Screen3_Switch1, 0);
    lv_obj_set_align(ui_Screen3_Switch1, LV_ALIGN_CENTER);

}
void ui_Screen4_screen_init(void)
{
    ui_Screen4 = lv_obj_create(NULL);
    lv_obj_clear_flag(ui_Screen4, LV_OBJ_FLAG_SCROLLABLE);      /// Flags

    ui_Screen1_Label4 = lv_label_create(ui_Screen4);
    lv_obj_set_width(ui_Screen1_Label4, LV_SIZE_CONTENT);   /// 1
    lv_obj_set_height(ui_Screen1_Label4, LV_SIZE_CONTENT);    /// 1
    lv_obj_set_x(ui_Screen1_Label4, 2);
    lv_obj_set_y(ui_Screen1_Label4, -98);
    lv_obj_set_align(ui_Screen1_Label4, LV_ALIGN_CENTER);
    lv_label_set_text(ui_Screen1_Label4, "Spinner");
    lv_obj_set_style_text_font(ui_Screen1_Label4, &lv_font_montserrat_24, LV_PART_MAIN | LV_STATE_DEFAULT);

    ui_Screen4_Spinner1 = lv_spinner_create(ui_Screen4, 1000, 90);
    lv_obj_set_width(ui_Screen4_Spinner1, 80);
    lv_obj_set_height(ui_Screen4_Spinner1, 80);
    lv_obj_set_align(ui_Screen4_Spinner1, LV_ALIGN_CENTER);
    lv_obj_clear_flag(ui_Screen4_Spinner1, LV_OBJ_FLAG_CLICKABLE);      /// Flags

}

void ui_init(void)
{
    lv_disp_t * dispp = lv_disp_get_default();
    lv_theme_t * theme = lv_theme_default_init(dispp, lv_palette_main(LV_PALETTE_BLUE), lv_palette_main(LV_PALETTE_RED),
                                               false, LV_FONT_DEFAULT);
    lv_disp_set_theme(dispp, theme);
    ui_Screen1_screen_init();
    ui_Screen2_screen_init();
    ui_Screen3_screen_init();
    ui_Screen4_screen_init();
    lv_disp_load_scr(ui_Screen1);
}
