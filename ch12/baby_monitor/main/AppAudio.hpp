// https://docs.espressif.com/projects/esp-idf/en/v4.4.6/esp32s3/api-guides/memory-types.html
// https://docs.espressif.com/projects/esp-idf/en/v4.4.6/esp32s3/api-guides/performance/ram-usage.html
// https://docs.espressif.com/projects/esp-idf/en/v4.4.6/esp32s3/api-guides/performance/size.html

#pragma once

#include <cstring>
#include <mutex>
#include <functional>
#include "freertos/FreeRTOS.h"
#include "freertos/task.h"
#include "sdkconfig.h"

#include "edge-impulse-sdk/classifier/ei_run_classifier.h"
#include "dl_lib_coefgetter_if.h"
#include "esp_afe_sr_models.h"
#include "esp_board_init.h"
#include "model_path.h"

namespace app
{

    class AppAudio
    {
    private:
        static constexpr int CRYING_IDX{0};
        static constexpr int NOISE_IDX{1};

        static constexpr int AUDIO_BUFFER_SIZE{16000};
        float *m_audio_buffer;
        float *m_features;
        int m_audio_buffer_ptr{0};
        std::mutex m_features_mutex;

        static constexpr int DETECT_TASK_BUFF_SIZE{4 * 1024};
        inline static uint8_t *m_detect_task_buffer;
        inline static StaticTask_t m_detect_task_data;

        static constexpr int ACTION_TASK_BUFF_SIZE{4 * 1024};
        inline static uint8_t *m_action_task_buffer;
        inline static StaticTask_t m_action_task_data;

        static constexpr int FEED_TASK_BUFF_SIZE{8 * 1024};
        inline static uint8_t m_feed_task_buffer[FEED_TASK_BUFF_SIZE];
        inline static StaticTask_t m_feed_task_data;

        esp_afe_sr_iface_t *m_afe_handle{nullptr};
        esp_afe_sr_data_t *m_afe_data{nullptr};

        std::function<void(bool)> m_crying_fn;
        bool m_crying;

        static void feedTask(void *arg);
        static void detectTask(void *arg);
        static void actionTask(void *arg);
        static afe_config_t defaultAfeConfig();

    public:
        void init(std::function<void(bool)> f)
        {
            m_crying_fn = f;
            m_crying = false;

            m_audio_buffer = new float[AUDIO_BUFFER_SIZE];
            m_features = new float[AUDIO_BUFFER_SIZE];

            m_detect_task_buffer = new uint8_t[DETECT_TASK_BUFF_SIZE];
            m_action_task_buffer = new uint8_t[ACTION_TASK_BUFF_SIZE];

            esp_board_init(AUDIO_HAL_16K_SAMPLES, 1, 16);
            m_afe_handle = const_cast<esp_afe_sr_iface_t *>(&ESP_AFE_VC_HANDLE);
            afe_config_t afe_config = defaultAfeConfig();
            m_afe_data = m_afe_handle->create_from_config(&afe_config);
        }

        void start(void)
        {
            xTaskCreateStaticPinnedToCore(feedTask, "feed", FEED_TASK_BUFF_SIZE, this, 5, m_feed_task_buffer, &m_feed_task_data, 0);
            xTaskCreateStaticPinnedToCore(detectTask, "detect", DETECT_TASK_BUFF_SIZE, this, 5, m_detect_task_buffer, &m_detect_task_data, 1);
            xTaskCreateStaticPinnedToCore(actionTask, "action", ACTION_TASK_BUFF_SIZE, this, 5, m_action_task_buffer, &m_action_task_data, 1);
        }
    };

    void AppAudio::feedTask(void *arg)
    {
        AppAudio *obj{static_cast<AppAudio *>(arg)};

        int audio_chunksize = obj->m_afe_handle->get_feed_chunksize(obj->m_afe_data);
        int feed_channel = esp_get_feed_channel();
        int16_t *i2s_buff = new int16_t[audio_chunksize * feed_channel];

        while (true)
        {
            esp_get_feed_data(false, i2s_buff, audio_chunksize * sizeof(int16_t) * feed_channel);
            obj->m_afe_handle->feed(obj->m_afe_data, i2s_buff);
        }
    }

    void AppAudio::detectTask(void *arg)
    {
        AppAudio *obj{static_cast<AppAudio *>(arg)};
        int afe_chunksize{obj->m_afe_handle->get_fetch_chunksize(obj->m_afe_data)};

        while (true)
        {
            afe_fetch_result_t *res = obj->m_afe_handle->fetch(obj->m_afe_data);
            if (res == nullptr || res->ret_value == ESP_FAIL)
            {
                continue;
            }

            for (int i = 0; i < afe_chunksize; ++i)
            {
                obj->m_audio_buffer_ptr %= AUDIO_BUFFER_SIZE;
                obj->m_audio_buffer[obj->m_audio_buffer_ptr++] = res->data[i];
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

    void AppAudio::actionTask(void *arg)
    {
        AppAudio *obj{static_cast<AppAudio *>(arg)};
        ei_impulse_result_t result = {nullptr};

        auto get_data_fn = [&obj](size_t offset, size_t length, float *out_ptr) -> int
        {
            memcpy(out_ptr, obj->m_features + offset, length * sizeof(float));
            return 0;
        };

        while (true)
        {
            signal_t features_signal{get_data_fn, AUDIO_BUFFER_SIZE};
            int result_idx{NOISE_IDX};

            {
                std::lock_guard<std::mutex> guard(obj->m_features_mutex);
                if (run_classifier(&features_signal, &result) == EI_IMPULSE_OK)
                {
                    for (uint16_t i = 0; i < EI_CLASSIFIER_LABEL_COUNT; ++i)
                    {
                        if (result.classification[i].value > result.classification[result_idx].value)
                        {
                            result_idx = i;
                        }
                    }
                }
            }

            switch (result_idx)
            {
            case CRYING_IDX:
            {
                if (!obj->m_crying)
                {
                    obj->m_crying_fn(true);
                    obj->m_crying = true;
                }
            }
            break;
            case NOISE_IDX:
            {
                if (obj->m_crying)
                {
                    obj->m_crying_fn(false);
                    obj->m_crying = false;
                }
            }
            break;
            default:
                break;
            }

            vTaskDelay(pdMS_TO_TICKS(1000));
        }
    }

    afe_config_t AppAudio::defaultAfeConfig()
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
        };
    }
}
