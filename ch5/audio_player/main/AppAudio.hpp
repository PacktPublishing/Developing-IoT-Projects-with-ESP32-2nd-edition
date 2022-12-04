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
        QueueHandle_t m_event_queue;
        bool m_muted;

    public:
        AppAudio() : m_fp(nullptr),
                     m_vol{50},
                     m_player_state(AUDIO_PLAYER_STATE_IDLE),
                     m_event_queue(nullptr),
                     m_muted(false) {}
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

        uint8_t mute(bool m, bool toggle = false)
        {
            uint8_t val = 0;
            m_muted = toggle ? !m_muted : m;
            if (m_muted)
            {
                bsp_codec_set_mute(true);
            }
            else
            {
                bsp_codec_set_mute(false);
                bsp_codec_set_voice_volume(m_vol);
                val = m_vol;
            }
            return val;
        }

        void togglePlay(const std::string &filename)
        {

            switch (m_player_state)
            {
            case AUDIO_PLAYER_STATE_PLAYING:
                ESP_LOGI(__func__, "%d - pausing", m_player_state);
                audio_player_pause();
                break;
            case AUDIO_PLAYER_STATE_PAUSE:
                ESP_LOGI(__func__, "%d - resuming", m_player_state);
                audio_player_resume();
                break;
            default:
                ESP_LOGI(__func__, "%d - playing", m_player_state);
                m_fp = fopen(filename.c_str(), "rb");
                audio_player_play(m_fp);
                break;
            }
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
            ESP_LOGI(__func__, "%d -> %d", m_player_state, state);
            m_player_state = state;
        }
    };
}

namespace
{
    void audio_player_callback(audio_player_cb_ctx_t *param)
    {
        app::AppAudio &app_audio = *(reinterpret_cast<app::AppAudio *>(param->user_ctx));
        audio_player_state_t state = audio_player_get_state();
        ESP_LOGI(__func__, "%d %d", param->audio_event, state);
        app_audio.setState(state);
        app::eAudioEvent evt = state == AUDIO_PLAYER_STATE_PLAYING ? app::eAudioEvent::PLAYING : app::eAudioEvent::STOPPED;
        xQueueSend(app_audio.getEventQueue(), (void *)(&evt), 0);
    }
}