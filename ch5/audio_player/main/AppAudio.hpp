#pragma once

#include <cstdio>
#include <cinttypes>
#include <string>

#include "freertos/FreeRTOS.h"
#include "freertos/queue.h"

#include "esp_err.h"
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

            audio_player_config_t config = {.mute_fn = fn,
                                            .clk_set_fn = bsp_codec_set_fs,
                                            .write_fn = bsp_i2s_write,
                                            .priority = 1};
            audio_player_new(config);
            audio_player_callback_register(audio_player_callback, this);

            int audio_resp;
            bsp_codec_volume_set(50, &audio_resp);

            m_event_queue = xQueueCreate(10, sizeof(app::eBtnEvent));
        }

        QueueHandle_t getEventQueue(void) const { return m_event_queue; }

        uint8_t mute(bool m, bool toggle = false)
        {
            uint8_t val = 0;
            m_muted = toggle ? !m_muted : m;
            if (m_muted)
            {
                bsp_codec_mute_set(true);
            }
            else
            {
                bsp_codec_mute_set(false);
                int audio_resp;
                bsp_codec_volume_set(m_vol, &audio_resp);
                val = ((uint8_t)audio_resp) % 100;
            }
            return val;
        }

        void togglePlay(const std::string &filename)
        {

            switch (m_player_state)
            {
            case AUDIO_PLAYER_STATE_PLAYING:
                audio_player_pause();
                break;
            case AUDIO_PLAYER_STATE_PAUSE:
                audio_player_resume();
                break;
            default:
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
                int audio_resp;
                bsp_codec_volume_set(m_vol, &audio_resp);
            }
            return m_vol;
        }

        uint8_t volumeDown(void)
        {
            if (m_vol > 0)
            {
                m_vol -= 10;
                int audio_resp;
                bsp_codec_volume_set(m_vol, &audio_resp);
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
        app::AppAudio &app_audio = *(reinterpret_cast<app::AppAudio *>(param->user_ctx));
        audio_player_state_t state = audio_player_get_state();
        app_audio.setState(state);
        app::eAudioEvent evt = state == AUDIO_PLAYER_STATE_PLAYING ? app::eAudioEvent::PLAYING : app::eAudioEvent::STOPPED;
        xQueueSend(app_audio.getEventQueue(), (void *)(&evt), 0);
    }
}