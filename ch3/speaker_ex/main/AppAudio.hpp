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
    };
}