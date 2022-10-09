#pragma once

#include <cinttypes>
#include "esp_err.h"
#include "esp_log.h"
#include "bsp_codec.h"
#include "bsp_board.h"
#include "bsp_storage.h"
#include "audio_player.h"
#include "file_iterator.h"

#include "AppSettings.hpp"

namespace app
{
    class AppAudio
    {
    private:
        AppSettings &m_settings;
        bool m_playing;
        file_iterator_instance_t *file_iterator;

    public:
        AppAudio(AppSettings &settings) : m_settings(settings), m_playing(false) {}
        void init(audio_player_mute_fn fn)
        {
            ESP_ERROR_CHECK(bsp_board_init());
            ESP_ERROR_CHECK(bsp_board_power_ctrl(POWER_MODULE_AUDIO, true));
            ESP_ERROR_CHECK(bsp_spiffs_init("storage", "/spiffs", 2));

            audio_player_config_t config = {.port = I2S_NUM_0,
                                            .mute_fn = fn,
                                            .priority = 1};
            ESP_ERROR_CHECK(audio_player_new(config));

            file_iterator = file_iterator_new("/spiffs/mp3");
        }

        void mute(bool m)
        {
            bsp_codec_set_mute(m);
            if (!m)
            {
                bsp_codec_set_voice_volume(m_settings.getVolume());
            }
            ESP_LOGI(__func__, "%s, volume:%d", m ? "muted" : "unmuted", m_settings.getVolume());
        }

        void play(void)
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
                    ESP_LOGE(__func__, "unable to open '%s'", filename);
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

        void volume_up(void)
        {
            uint8_t volume = m_settings.getVolume();
            if (volume < 100)
            {
                volume += 10;
                ESP_LOGI(__func__, "volume up (%d)", volume);
                bsp_codec_set_voice_volume(volume);
                m_settings.updateVolume(volume);
            }
        }

        void volume_down(void)
        {
            uint8_t volume = m_settings.getVolume();
            if (volume > 0)
            {
                volume -= 10;
                ESP_LOGI(__func__, "volume down (%d)", volume);
                bsp_codec_set_voice_volume(volume);
                m_settings.updateVolume(volume);
            }
        }
    };
}