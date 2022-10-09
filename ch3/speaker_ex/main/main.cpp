#include "AppSettings.hpp"
#include "AppAudio.hpp"
#include "AppButton.hpp"

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
        m_app_audio.play();
    }

    void volume_up(void *data)
    {
        m_app_audio.volume_up();
    }

    void volume_down(void *data)
    {
        m_app_audio.volume_down();
    }
}

extern "C" void app_main(void)
{
    m_app_settings.init();
    m_app_audio.init(audio_mute_function);
    m_app_btn.init(play_music, volume_down, volume_up);
}
