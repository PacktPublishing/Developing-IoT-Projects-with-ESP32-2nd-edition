#pragma once

#include <cstdlib>
#include "freertos/FreeRTOS.h"
#include "freertos/task.h"
#include "esp_log.h"

#include "esp_wn_iface.h"
#include "esp_wn_models.h"
#include "esp_afe_sr_iface.h"
#include "esp_afe_sr_models.h"
#include "esp_mn_iface.h"
#include "esp_mn_models.h"
#include "esp_board_init.h"
#include "model_path.h"
#include "esp_process_sdkconfig.h"

#include "AppLed.hpp"

#define CMD_NONE -1
#define CMD_POWER_ON 0
#define CMD_POWER_OFF 1
#define CMD_RED 2
#define CMD_GREEN 3
#define CMD_BLUE 4

#define LISTEN_CMD_TIMEOUT 6000

namespace app
{
    class AppSpeech
    {
    private:
        esp_afe_sr_iface_t *m_afe_handle{nullptr};
        esp_afe_sr_data_t *m_afe_data{nullptr};
        srmodel_list_t *m_models{nullptr};
        static constexpr const char *TAG{"speech"};
        AppLed m_led;

        static afe_config_t defaultAfeConfig();
        static void feedTask(void *arg);
        static void detectTask(void *arg);
        void handleCommand(esp_mn_iface_t *multinet, model_iface_data_t *model_data);

    public:
        void start(void)
        {
            esp_board_init(16000, 1, 16);
            m_led.init();

            m_models = esp_srmodel_init("model");
            m_afe_handle = const_cast<esp_afe_sr_iface_t *>(&ESP_AFE_SR_HANDLE);

            afe_config_t afe_config = defaultAfeConfig();
            afe_config.wakenet_model_name = esp_srmodel_filter(m_models, ESP_WN_PREFIX, nullptr);
            m_afe_data = m_afe_handle->create_from_config(&afe_config);

            xTaskCreatePinnedToCore(detectTask, "detect", 8 * 1024, this, 5, nullptr, 1);
            xTaskCreatePinnedToCore(feedTask, "feed", 8 * 1024, this, 5, nullptr, 0);
        }
    };

    void AppSpeech::feedTask(void *arg)
    {
        AppSpeech *obj = static_cast<AppSpeech *>(arg);

        size_t buff_size = obj->m_afe_handle->get_feed_chunksize(obj->m_afe_data) * esp_get_feed_channel() * sizeof(int16_t);
        int16_t *audio_buffer = static_cast<int16_t *>(malloc(buff_size));

        while (1)
        {
            esp_get_feed_data(false, audio_buffer, buff_size);
            obj->m_afe_handle->feed(obj->m_afe_data, audio_buffer);
        }
    }

    void AppSpeech::handleCommand(esp_mn_iface_t *multinet, model_iface_data_t *model_data)
    {
        int cmd = CMD_NONE;

        esp_mn_results_t *mn_result = multinet->get_results(model_data);
        ESP_LOGI(TAG, "detection results:");
        for (int i = 0; i < mn_result->num; i++)
        {
            ESP_LOGI(TAG, "- cmd:%d prob:%f", mn_result->command_id[i], mn_result->prob[i]);
            if (mn_result->prob[i] > 0.5)
            {
                cmd = mn_result->command_id[i];
                break;
            }
        }

        switch (cmd)
        {
        case CMD_POWER_ON:
            m_led.on();
            break;
        case CMD_POWER_OFF:
            m_led.off();
            break;
        case CMD_RED:
            m_led.setColor(eColor::Red);
            break;
        case CMD_GREEN:
            m_led.setColor(eColor::Green);
            break;
        case CMD_BLUE:
            m_led.setColor(eColor::Blue);
            break;

        default:
            break;
        }
    }

    void AppSpeech::detectTask(void *arg)
    {
        AppSpeech *obj = static_cast<AppSpeech *>(arg);
        bool listen_command = false;

        char *mn_name = esp_srmodel_filter(obj->m_models, ESP_MN_PREFIX, ESP_MN_ENGLISH);
        esp_mn_iface_t *multinet = esp_mn_handle_from_name(mn_name);
        model_iface_data_t *model_data = multinet->create(mn_name, LISTEN_CMD_TIMEOUT);
        esp_mn_commands_update_from_sdkconfig(multinet, model_data);

        ESP_LOGI(TAG, "waiting wake-word");
        while (1)
        {
            afe_fetch_result_t *res = obj->m_afe_handle->fetch(obj->m_afe_data);

            switch (res->wakeup_state)
            {
            case WAKENET_DETECTED:
                multinet->clean(model_data);
                break;
            case WAKENET_CHANNEL_VERIFIED:
                listen_command = true;
                ESP_LOGI(TAG, "waiting command");
            default:
                break;
            }

            if (listen_command)
            {
                switch (multinet->detect(model_data, res->data))
                {
                case ESP_MN_STATE_TIMEOUT:
                    obj->m_afe_handle->enable_wakenet(obj->m_afe_data);
                    listen_command = false;
                    ESP_LOGI(TAG, "waiting wake-word");
                    break;

                case ESP_MN_STATE_DETECTED:
                    obj->handleCommand(multinet, model_data);

                default:
                    break;
                }
            }
        }
    }

    afe_config_t AppSpeech::defaultAfeConfig()
    {
        afe_config_t afe_config = {.debug_hook = {{AFE_DEBUG_HOOK_MASE_TASK_IN, NULL}, {AFE_DEBUG_HOOK_FETCH_TASK_IN, NULL}}};

        afe_config.aec_init = true;
        afe_config.se_init = true;
        afe_config.vad_init = true;
        afe_config.wakenet_init = true;
        afe_config.voice_communication_init = false;
        afe_config.voice_communication_agc_init = false;
        afe_config.voice_communication_agc_gain = 15;
        afe_config.vad_mode = VAD_MODE_3;
        afe_config.wakenet_model_name = NULL;
        afe_config.wakenet_model_name_2 = NULL;
        afe_config.wakenet_mode = DET_MODE_2CH_90;
        afe_config.afe_mode = SR_MODE_LOW_COST;
        afe_config.afe_perferred_core = 0;
        afe_config.afe_perferred_priority = 5;
        afe_config.afe_ringbuf_size = 50;
        afe_config.memory_alloc_mode = AFE_MEMORY_ALLOC_MORE_PSRAM;
        afe_config.afe_linear_gain = 1.0;
        afe_config.agc_mode = AFE_MN_PEAK_AGC_MODE_2;
        afe_config.debug_init = false;
        afe_config.afe_ns_mode = NS_MODE_SSP;
        afe_config.afe_ns_model_name = NULL;

        afe_config.pcm_config.total_ch_num = 3;
        afe_config.pcm_config.mic_num = 2;
        afe_config.pcm_config.ref_num = 1;
        afe_config.pcm_config.sample_rate = 16000;

        afe_config.aec_init = false;
        return afe_config;
    }
} // namespace app
