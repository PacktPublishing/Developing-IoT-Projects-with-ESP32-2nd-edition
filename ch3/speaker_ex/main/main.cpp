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
#include "AppAudio.hpp"
#include "AppButton.hpp"

static const char *TAG = "main";
file_iterator_instance_t *file_iterator;

namespace
{
    app::AppSettings m_app_settings;
    app::AppAudio m_app_audio(m_app_settings);
    app::AppButton m_app_btn;

    esp_err_t audio_mute_function(AUDIO_PLAYER_MUTE_SETTING setting)
    {
        m_app_audio.mute(setting == AUDIO_PLAYER_MUTE);
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
}

extern "C" void app_main(void)
{
    ESP_LOGI(TAG, "Compile time: %s %s", __DATE__, __TIME__);

    m_app_settings.init();
    m_app_audio.init(audio_mute_function);

    file_iterator = file_iterator_new("/spiffs/mp3");
    assert(file_iterator != NULL);

    m_app_btn.init(play_music, volume_down, volume_up);
    // bsp_btn_register_callback(BOARD_BTN_ID_PREV, BUTTON_PRESS_DOWN, play_music, NULL);
    // bsp_btn_register_callback(BOARD_BTN_ID_ENTER, BUTTON_PRESS_DOWN, volume_down, NULL);
    // bsp_btn_register_callback(BOARD_BTN_ID_NEXT, BUTTON_PRESS_DOWN, volume_up, NULL);
}
