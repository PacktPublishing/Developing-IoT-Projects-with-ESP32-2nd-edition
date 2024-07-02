
#pragma once

#include <vector>
#include <cinttypes>
#include <memory>
#include "esp_log.h"
#include "freertos/FreeRTOS.h"
#include "freertos/task.h"
#include "esp_adc/adc_oneshot.h"

#include "flatbuffers/idl.h"
#include "flatbuffers/util.h"
#include "app_data_generated.h"

namespace app
{
    class AppLdrLogger
    {
    private:
        LightSensorFbT m_light_sensor;
        const adc_channel_t m_adc1_ch = ADC_CHANNEL_8;
        adc_oneshot_unit_handle_t m_adc1_handle;

    public:
        void init(void)
        {
            adc_oneshot_unit_init_cfg_t init_config1 = {
                .unit_id = ADC_UNIT_1,
            };
            ESP_ERROR_CHECK(adc_oneshot_new_unit(&init_config1, &m_adc1_handle));

            adc_oneshot_chan_cfg_t config = {
                .atten = ADC_ATTEN_DB_12,
                .bitwidth = ADC_BITWIDTH_12,
            };
            ESP_ERROR_CHECK(adc_oneshot_config_channel(m_adc1_handle, m_adc1_ch, &config));

            // adc1_config_width(ADC_WIDTH_BIT_12);
            // adc1_config_channel_atten(m_adc1_ch, ADC_ATTEN_DB_12);
            m_light_sensor.location = "office";
        }

        void run(void)
        {
            while (1)
            {
                vTaskDelay(pdMS_TO_TICKS(5000));

                int adc_val = 0;

                ESP_ERROR_CHECK(adc_oneshot_read(m_adc1_handle, m_adc1_ch, &adc_val));

                auto reading = std::unique_ptr<ReadingFbT>(new ReadingFbT());
                reading->timestamp = esp_log_timestamp();
                reading->light = (uint16_t)adc_val;
                m_light_sensor.readings.push_back(std::move(reading));
            }
        }

        size_t serialize(uint8_t *buffer)
        {
            flatbuffers::FlatBufferBuilder fbb;
            fbb.Finish(LightSensorFb::Pack(fbb, &m_light_sensor));
            memcpy(buffer, fbb.GetBufferPointer(), fbb.GetSize());
            size_t len = fbb.GetSize();
            m_light_sensor.readings.clear();
            return len;
        }
    };
}
