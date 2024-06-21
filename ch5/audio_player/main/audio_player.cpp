#include "bsp_board.h"

#include "AppUi.hpp"
#include "AppButton.hpp"
#include "AppAudio.hpp"

namespace
{
    app::AppButton m_app_btn;
    app::AppAudio m_app_audio;
    app::AppUi m_app_ui;

    esp_err_t audio_mute_function(AUDIO_PLAYER_MUTE_SETTING setting)
    {
        m_app_audio.mute(setting == AUDIO_PLAYER_MUTE);
        return ESP_OK;
    }
}

extern "C" void app_main(void)
{
    bsp_i2c_init();
    bsp_spiffs_mount();

    // LVGL initialisation is on BSP
    bsp_display_cfg_t cfg = {
        .lvgl_port_cfg = ESP_LVGL_PORT_INIT_CONFIG(),
        .buffer_size = BSP_LCD_H_RES * CONFIG_BSP_LCD_DRAW_BUF_HEIGHT,
        .double_buffer = 0,
        .flags = {
            .buff_dma = true,
        }};
    bsp_display_start_with_config(&cfg);
    bsp_display_backlight_on();
    bsp_board_init();

    // bsp_board_init();
    // bsp_board_power_ctrl(POWER_MODULE_AUDIO, true);
    // bsp_spiffs_init("storage", "/spiffs", 10);

    m_app_btn.init();
    m_app_audio.init(audio_mute_function);
    m_app_ui.init(&m_app_btn, &m_app_audio);
}
