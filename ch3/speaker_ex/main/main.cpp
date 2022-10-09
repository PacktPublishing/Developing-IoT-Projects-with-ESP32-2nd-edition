/*
 * SPDX-FileCopyrightText: 2015-2022 Espressif Systems (Shanghai) CO LTD
 *
 * SPDX-License-Identifier: Unlicense OR CC0-1.0
 */

#include <stdio.h>
#include "esp_heap_caps.h"
#include "esp_log.h"
#include "freertos/FreeRTOS.h"
#include "freertos/task.h"
#include "esp_log.h"
#include "esp_check.h"
// #include "nvs_flash.h"
// #include "nvs.h"
#include "bsp_codec.h"
#include "bsp_board.h"
#include "bsp_btn.h"
#include "bsp_storage.h"
#include "audio_player.h"
#include "file_iterator.h"

#include "AppSettings.hpp"

static const char *TAG = "main";

namespace
{
    app::cAppSettings m_app_settings;
}

file_iterator_instance_t *file_iterator;

static esp_err_t audio_mute_function(AUDIO_PLAYER_MUTE_SETTING setting)
{
    // Volume saved when muting and restored when unmuting. Restoring volume is necessary
    // as es8311_set_voice_mute(true) results in voice volume (REG32) being set to zero.

    ESP_RETURN_ON_ERROR(bsp_codec_set_mute(setting == AUDIO_PLAYER_MUTE ? true : false), TAG, "set voice mute");

    // restore the voice volume upon unmuting
    if (setting == AUDIO_PLAYER_UNMUTE)
    {
        bsp_codec_set_voice_volume(m_app_settings.getVolume());
    }

    ESP_LOGI(TAG, "mute setting %d, volume:%d", setting, m_app_settings.getVolume());

    return ESP_OK;
}

void play_music(void *data)
{
    ESP_LOGI(__func__, "button play");
    static bool playing = false;
    if (!playing)
    {
        char filename[128];
        file_iterator_get_full_path_from_index(file_iterator, file_iterator_get_index(file_iterator), filename, sizeof(filename));
        FILE *fp = fopen(filename, "rb");
        if (!fp)
        {
            ESP_LOGE(TAG, "unable to open '%s'", filename);
            return;
        }
        else
        {
            ESP_LOGI(__func__, "playing %s", filename);
        }
        audio_player_play(fp);
    }
    else
    {
        audio_player_pause();
    }

    playing = !playing;
}

void volume_up(void *data)
{
    uint8_t volume = m_app_settings.getVolume();
    if (volume < 100)
    {
        volume += 10;
        ESP_LOGI(__func__, "volume up (%d)", volume);
        bsp_codec_set_voice_volume(volume);
        m_app_settings.updateVolume(volume);
    }
}

void volume_down(void *data)
{
    uint8_t volume = m_app_settings.getVolume();
    if (volume > 0)
    {
        volume -= 10;
        ESP_LOGI(__func__, "volume down (%d)", volume);
        bsp_codec_set_voice_volume(volume);
        m_app_settings.updateVolume(volume);
    }
}

extern "C" void app_main(void)
{
    ESP_LOGI(TAG, "Compile time: %s %s", __DATE__, __TIME__);
    
    m_app_settings.init();

    ESP_ERROR_CHECK(bsp_board_init());
    ESP_ERROR_CHECK(bsp_board_power_ctrl(POWER_MODULE_AUDIO, true));
    ESP_ERROR_CHECK(bsp_spiffs_init("storage", "/spiffs", 2));
    file_iterator = file_iterator_new("/spiffs/mp3");
    assert(file_iterator != NULL);
    audio_player_config_t config = {.port = I2S_NUM_0,
                                    .mute_fn = audio_mute_function,
                                    .priority = 1};
    ESP_ERROR_CHECK(audio_player_new(config));

    bsp_btn_register_callback(BOARD_BTN_ID_PREV, BUTTON_PRESS_DOWN, play_music, NULL);
    bsp_btn_register_callback(BOARD_BTN_ID_ENTER, BUTTON_PRESS_DOWN, volume_down, NULL);
    bsp_btn_register_callback(BOARD_BTN_ID_NEXT, BUTTON_PRESS_DOWN, volume_up, NULL);
}
