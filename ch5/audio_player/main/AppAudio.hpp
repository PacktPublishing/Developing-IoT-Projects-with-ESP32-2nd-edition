#pragma once

#include <cstdio>
#include <cinttypes>
#include "esp_err.h"
#include "bsp_codec.h"
#include "bsp_board.h"
#include "bsp_storage.h"
#include "audio_player.h"

namespace app
{
    class AppAudio
    {
    private:
        bool m_playing;
        FILE *m_fp;
        uint8_t m_vol;

    public:
        AppAudio() : m_playing(false), m_fp(nullptr), m_vol{50} {}
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
                bsp_codec_set_voice_volume(m_vol);
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
            if (m_vol < 100)
            {
                m_vol += 10;
                bsp_codec_set_voice_volume(m_vol);
            }
        }

        void volume_down(void)
        {
            if (m_vol > 0)
            {
                m_vol -= 10;
                bsp_codec_set_voice_volume(m_vol);
            }
        }
    };
}