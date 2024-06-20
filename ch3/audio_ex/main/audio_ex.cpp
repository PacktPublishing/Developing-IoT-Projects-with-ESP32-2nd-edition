#include "bsp_board.h"
#include "bsp_storage.h"

#include "AppSettings.hpp"
#include "AppAudio.hpp"
#include "AppButton.hpp"

namespace
{
    app::AppSettings m_app_settings;
    app::AppAudio m_app_audio(m_app_settings);
    app::AppButton m_app_btn;

    esp_err_t audio_mute_function(AUDIO_PLAYER_MUTE_SETTING setting);
    void play_music(void *handle, void *data);
    void volume_up(void *handle, void *data);
    void volume_down(void *handle, void *data);
}

extern "C" void app_main(void)
{
    bsp_i2c_init();
    bsp_spiffs_mount();
    bsp_board_init();

    m_app_settings.init();
    m_app_audio.init(audio_mute_function);
    m_app_btn.init(play_music, volume_down, volume_up);
}

namespace
{
    
    void play_music(void *handle, void *data)
    {
        m_app_audio.play();
    }

    void volume_up(void *handle, void *data)
    {
        m_app_audio.volume_up();
    }

    void volume_down(void *handle, void *data)
    {
        m_app_audio.volume_down();
    }

    esp_err_t audio_mute_function(AUDIO_PLAYER_MUTE_SETTING setting)
    {
        m_app_audio.mute(setting == AUDIO_PLAYER_MUTE);
        return ESP_OK;
    }

}
