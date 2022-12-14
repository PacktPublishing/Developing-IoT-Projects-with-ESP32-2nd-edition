
#pragma once

#include <vector>
#include <cinttypes>
#include <memory>
#include "esp_log.h"
#include "freertos/FreeRTOS.h"
#include "freertos/task.h"
#include "driver/adc.h"

#include "flatbuffers/idl.h"
#include "flatbuffers/util.h"
#include "app_data_generated.h"

namespace app
{
    class AppLdrLogger
    {
    private:
        LightSensorFbT m_light_sensor;
        const adc1_channel_t m_adc_ch = ADC1_CHANNEL_8;

    public:
        void init(void)
        {
            adc1_config_width(ADC_WIDTH_BIT_12);
            adc1_config_channel_atten(m_adc_ch, ADC_ATTEN_DB_11);
            m_light_sensor.location = "office";
        }

        void run(void)
        {
            while (1)
            {
                vTaskDelay(pdMS_TO_TICKS(5000));

                uint32_t adc_val = 0;
                for (int i = 0; i < 32; ++i)
                {
                    adc_val += adc1_get_raw(m_adc_ch);
                }
                adc_val /= 32;
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
