#pragma once

#include <cstring>
#include <mutex>
#include <functional>
#include "freertos/FreeRTOS.h"
#include "freertos/task.h"
#include "sdkconfig.h"

#include "edge-impulse-sdk/classifier/ei_run_classifier.h"
#include "esp_wn_iface.h"
#include "esp_wn_models.h"
#include "dl_lib_coefgetter_if.h"
#include "esp_afe_sr_models.h"
#include "esp_mn_iface.h"
#include "esp_mn_models.h"
#include "esp_board_init.h"
#include "model_path.h"

#define NOISE_IDX 0
#define UNKNOWN_IDX 1
#define TINYML_IDX 2

namespace app
{
    struct AppSpeechParam
    {
        std::function<void(void)> noise_fn;
        std::function<void(void)> unknown_fn;
        std::function<void(void)> tinyml_fn;
    };

    class AppSpeech
    {
    private:
        static constexpr int AUDIO_BUFFER_SIZE{16000};
        int m_audio_buffer_ptr{0};
        float m_audio_buffer[AUDIO_BUFFER_SIZE];
        float m_features[AUDIO_BUFFER_SIZE];
        std::mutex m_features_mutex;

        esp_afe_sr_iface_t *m_afe_handle{nullptr};
        esp_afe_sr_data_t *m_afe_data{nullptr};

        AppSpeechParam m_callbacks;

        static void feedTask(void *arg)
        {
            AppSpeech *obj{static_cast<AppSpeech *>(arg)};
            esp_afe_sr_data_t *afe_data{obj->m_afe_data};
            esp_afe_sr_iface_t *afe_handle{obj->m_afe_handle};

            int audio_chunksize = afe_handle->get_feed_chunksize(afe_data);
            int feed_channel = esp_get_feed_channel();
            int16_t *i2s_buff = static_cast<int16_t *>(malloc(audio_chunksize * sizeof(int16_t) * feed_channel));

            while (true)
            {
                esp_get_feed_data(false, i2s_buff, audio_chunksize * sizeof(int16_t) * feed_channel);
                afe_handle->feed(afe_data, i2s_buff);
            }
        }

        static void detectTask(void *arg)
        {
            AppSpeech *obj{static_cast<AppSpeech *>(arg)};
            esp_afe_sr_data_t *afe_data{obj->m_afe_data};
            esp_afe_sr_iface_t *afe_handle{obj->m_afe_handle};

            int afe_chunksize = afe_handle->get_fetch_chunksize(afe_data);
            int16_t *buff = static_cast<int16_t *>(malloc(afe_chunksize * sizeof(int16_t)));

            while (true)
            {
                afe_fetch_result_t *res = afe_handle->fetch(afe_data);
                if (res == nullptr || res->ret_value == ESP_FAIL)
                {
                    continue;
                }

                memcpy(buff, res->data, afe_chunksize * sizeof(int16_t));

                for (int i = 0; i < afe_chunksize; ++i)
                {
                    obj->m_audio_buffer_ptr %= AUDIO_BUFFER_SIZE;
                    obj->m_audio_buffer[obj->m_audio_buffer_ptr++] = buff[i];
                }

                {
                    std::lock_guard<std::mutex> guard(obj->m_features_mutex);
                    for (int i = 0; i < AUDIO_BUFFER_SIZE; ++i)
                    {
                        obj->m_features[i] = obj->m_audio_buffer[(obj->m_audio_buffer_ptr + i) % AUDIO_BUFFER_SIZE];
                    }
                }
            }
        }

        static void actionTask(void *arg)
        {
            AppSpeech *obj{static_cast<AppSpeech *>(arg)};
            ei_impulse_result_t result = {nullptr};

            auto get_data_fn = [&obj](size_t offset, size_t length, float *out_ptr) -> int
            {
                memcpy(out_ptr, obj->m_features + offset, length * sizeof(float));
                return 0;
            };

            while (true)
            {
                signal_t features_signal{get_data_fn, AUDIO_BUFFER_SIZE};
                int max_idx = NOISE_IDX;

                {
                    std::lock_guard<std::mutex> guard(obj->m_features_mutex);
                    if (run_classifier(&features_signal, &result) == EI_IMPULSE_OK)
                    {
                        for (uint16_t i = 0; i < EI_CLASSIFIER_LABEL_COUNT; ++i)
                        {
                            if (result.classification[i].value > result.classification[max_idx].value)
                            {
                                max_idx = i;
                            }
                        }
                    }
                }

                switch (max_idx)
                {
                case NOISE_IDX:
                    obj->m_callbacks.noise_fn();
                    break;
                case UNKNOWN_IDX:
                    obj->m_callbacks.unknown_fn();
                    break;
                case TINYML_IDX:
                    obj->m_callbacks.tinyml_fn();
                    break;
                default:
                    break;
                }

                vTaskDelay(pdMS_TO_TICKS(1000));
            }
        }

        static afe_config_t defaultAfeConfig()
        {
            return {
                .aec_init = false,
                .se_init = true,
                .vad_init = false,
                .wakenet_init = false,
                .voice_communication_init = true,
                .voice_communication_agc_init = false,
                .voice_communication_agc_gain = 15,
                .vad_mode = VAD_MODE_3,
                .wakenet_model_name = nullptr,
                .wakenet_mode = DET_MODE_2CH_90,
                .afe_mode = SR_MODE_LOW_COST,
                .afe_perferred_core = 0,
                .afe_perferred_priority = 5,
                .afe_ringbuf_size = 50,
                .memory_alloc_mode = AFE_MEMORY_ALLOC_MORE_PSRAM,
                .agc_mode = AFE_MN_PEAK_AGC_MODE_2,
                .pcm_config = {3, 2, 1, 16000},
                .debug_init = false,
                .debug_hook = {{AFE_DEBUG_HOOK_MASE_TASK_IN, nullptr}, {AFE_DEBUG_HOOK_FETCH_TASK_IN, nullptr}},
            };
        }

    public:
        void init(AppSpeechParam cbs)
        {
            m_callbacks = cbs;
            esp_board_init(AUDIO_HAL_16K_SAMPLES, 1, 16);
            m_afe_handle = const_cast<esp_afe_sr_iface_t *>(&ESP_AFE_VC_HANDLE);
            afe_config_t afe_config = defaultAfeConfig();
            m_afe_data = m_afe_handle->create_from_config(&afe_config);
        }

        void start(void)
        {
            xTaskCreatePinnedToCore(feedTask, "feed", 8 * 1024, this, 5, nullptr, 0);
            xTaskCreatePinnedToCore(detectTask, "detect", 8 * 1024, this, 5, nullptr, 1);
            xTaskCreatePinnedToCore(actionTask, "action", 8 * 1024, this, 5, nullptr, 1);
        }
    };
}
