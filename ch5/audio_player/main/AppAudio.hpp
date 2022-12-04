#pragma once

#include <cstdio>
#include <cinttypes>
#include <string>

#include "freertos/FreeRTOS.h"
#include "freertos/queue.h"

#include "esp_err.h"
#include "bsp_codec.h"
#include "bsp_board.h"
#include "bsp_storage.h"
#include "audio_player.h"

namespace
{

    void audio_player_callback(audio_player_cb_ctx_t *obj);
}

namespace app
{
    enum class eAudioEvent
    {
        PLAYING,
        STOPPED
    };
}

namespace app
{
    class AppAudio
    {
    private:
        FILE *m_fp;
        uint8_t m_vol;

        audio_player_state_t m_player_state;
        QueueHandle_t m_event_queue = NULL;

    public:
        AppAudio() : m_fp(nullptr), m_vol{50}, m_player_state(AUDIO_PLAYER_STATE_IDLE) {}
        void init(audio_player_mute_fn fn)
        {

            audio_player_config_t config = {.port = I2S_NUM_0,
                                            .mute_fn = fn,
                                            .priority = 1};
            audio_player_new(config);
            audio_player_callback_register(audio_player_callback, this);
            bsp_codec_set_voice_volume(50);

            m_event_queue = xQueueCreate(10, sizeof(app::eBtnEvent));
        }

        QueueHandle_t getEventQueue(void) const { return m_event_queue; }

        void mute(bool m)
        {
            bsp_codec_set_mute(m);
            if (!m)
            {
                bsp_codec_set_voice_volume(m_vol);
            }
        }

        bool togglePlay(const std::string &filename, bool force_play = false)
        {
            ESP_LOGI(__func__, "%d", m_player_state);
            if (force_play)
            {
                m_fp = fopen(filename.c_str(), "rb");
                return audio_player_play(m_fp) == ESP_OK;
            }

            bool is_playing = m_player_state == AUDIO_PLAYER_STATE_PLAYING;
            if (is_playing)
            {
                audio_player_pause();
                return false;
            }

            if (m_player_state == AUDIO_PLAYER_STATE_PAUSE)
            {
                audio_player_resume();
                return true;
            }

            m_fp = fopen(filename.c_str(), "rb");
            return audio_player_play(m_fp) == ESP_OK;
        }

        uint8_t volumeUp(void)
        {
            if (m_vol < 100)
            {
                m_vol += 10;
                bsp_codec_set_voice_volume(m_vol);
            }
            return m_vol;
        }

        uint8_t volumeDown(void)
        {
            if (m_vol > 0)
            {
                m_vol -= 10;
                bsp_codec_set_voice_volume(m_vol);
            }
            return m_vol;
        }

        void setState(audio_player_state_t state)
        {
            m_player_state = state;
        }
    };
}

namespace
{
    void audio_player_callback(audio_player_cb_ctx_t *param)
    {
        app::AppAudio app_audio = *(reinterpret_cast<app::AppAudio *>(param->user_ctx));
        audio_player_state_t state = audio_player_get_state();
        app_audio.setState(state);
        app::eAudioEvent evt = state == AUDIO_PLAYER_STATE_PLAYING ? app::eAudioEvent::PLAYING : app::eAudioEvent::STOPPED;
        xQueueSend(app_audio.getEventQueue(), (void *)(&evt), 0);
        ESP_LOGI(__func__, "%d %d", param->audio_event, state);
    }
}