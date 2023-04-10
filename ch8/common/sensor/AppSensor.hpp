
#pragma once

#include <freertos/FreeRTOS.h>
#include <freertos/task.h>
#include "esp_log.h"
#include "driver/adc.h"

#include "AppSensorClient.hpp"

namespace app
{
    class AppSensor
    {
    private:
        AppSensorClient *m_client;
        const adc1_channel_t m_adc_ch{ADC1_CHANNEL_4}; // gpio4
        int m_period;

        static void readTask(void *arg);
        uint32_t readLight(void);

    public:
        void init(app::AppSensorClient *cl, int period)
        {
            m_client = cl;
            adc1_config_width(ADC_WIDTH_BIT_12);
            adc1_config_channel_atten(m_adc_ch, ADC_ATTEN_DB_11);

            m_period = period * 1000;
        }

        void start(void)
        {
            xTaskCreate(readTask, "sensor", 2048, this, 5, nullptr);
        }
    };

    void AppSensor::readTask(void *arg)
    {
        AppSensor *obj = reinterpret_cast<AppSensor *>(arg);
        while (1)
        {
            vTaskDelay(obj->m_period / portTICK_PERIOD_MS);
            obj->m_client->update(obj->readLight());
        }
    }

    uint32_t AppSensor::readLight(void)
    {
        uint32_t adc_val{0};
        for (int i = 0; i < 32; ++i)
        {
            adc_val += adc1_get_raw(m_adc_ch);
        }
        adc_val /= 32;
        return adc_val;
    }

}