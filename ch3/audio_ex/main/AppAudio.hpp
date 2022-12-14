#pragma once

#include <cstdio>
#include <cinttypes>
#include "esp_err.h"
#include "bsp_codec.h"
#include "bsp_board.h"
#include "bsp_storage.h"
#include "audio_player.h"

#include "AppSettings.hpp"

namespace app
{
    class AppAudio
    {
    private:
        AppSettings &m_settings;
        bool m_playing;
        FILE *m_fp;

    public:
        AppAudio(AppSettings &settings) : m_settings(settings), m_playing(false), m_fp(nullptr) {}
        void init(audio_player_mute_fn fn)
        {

            audio_player_config_t config = {.port = I2S_NUM_0,
                                            .mute_fn = fn,
                                            .priority = 1};
            audio_player_new(config);
        }

        void mute(bool m)
        {
            bsp_codec_set_mute(m);
            if (!m)
            {
                bsp_codec_set_voice_volume(m_settings.getVolume());
            }
        }

        void play(void)
        {
            if (!m_playing)
            {
                m_fp = fopen("/spiffs/mp3/music.mp3", "rb");
                audio_player_play(m_fp);
            }
            else
            {
                audio_player_pause();
            }

            m_playing = !m_playing;
        }

        void volume_up(void)
        {
            uint8_t volume = m_settings.getVolume();
            if (volume < 100)
            {
                volume += 10;
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
                bsp_codec_set_voice_volume(volume);
                m_settings.updateVolume(volume);
            }
        }
    };
}