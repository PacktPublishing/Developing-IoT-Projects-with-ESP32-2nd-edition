// SquareLine LVGL GENERATED FILE
// EDITOR VERSION: SquareLine Studio 1.1.1
// LVGL VERSION: 8.2.0
// PROJECT: audio_player

#ifndef _AUDIO_PLAYER_UI_H
#define _AUDIO_PLAYER_UI_H

#ifdef __cplusplus
extern "C" {
#endif

#include "lvgl.h"

extern lv_obj_t * ui_Screen1;
void ui_event_btnPlay(lv_event_t * e);
extern lv_obj_t * ui_btnPlay;
extern lv_obj_t * ui_txtPlayButton;
void ui_event_barVolume(lv_event_t * e);
extern lv_obj_t * ui_barVolume;
extern lv_obj_t * ui_txtAnimal;
void ui_event_btnVolumeDown(lv_event_t * e);
extern lv_obj_t * ui_btnVolumeDown;
void ui_event_btnVolumeUp(lv_event_t * e);
extern lv_obj_t * ui_btnVolumeUp;
void ui_event_btnPrev(lv_event_t * e);
extern lv_obj_t * ui_btnPrev;
void ui_event_btnNext(lv_event_t * e);
extern lv_obj_t * ui_btnNext;
extern lv_obj_t * ui_imgAnimal;

void play_clicked(lv_event_t * e);
void play_focused(lv_event_t * e);
void volume_focused(lv_event_t * e);
void vdown_clicked(lv_event_t * e);
void vup_clicked(lv_event_t * e);
void prev_clicked(lv_event_t * e);
void next_clicked(lv_event_t * e);

LV_IMG_DECLARE(ui_img_1552218578);    // assets/down-f.png
LV_IMG_DECLARE(ui_img_1552235971);    // assets/down-w.png
LV_IMG_DECLARE(ui_img_1258062811);    // assets/up-f.png
LV_IMG_DECLARE(ui_img_1258080204);    // assets/up-w.png
LV_IMG_DECLARE(ui_img_603081905);    // assets/prev-f.png
LV_IMG_DECLARE(ui_img_603097248);    // assets/prev-w.png
LV_IMG_DECLARE(ui_img_1310788941);    // assets/next-f.png
LV_IMG_DECLARE(ui_img_1310804284);    // assets/next-w.png




void ui_init(void);

#ifdef __cplusplus
} /*extern "C"*/
#endif

#endif
