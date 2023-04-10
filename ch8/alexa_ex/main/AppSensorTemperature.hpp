#pragma once

#include <freertos/FreeRTOS.h>
#include <freertos/task.h>
#include "esp_log.h"
#include "driver/gpio.h"
#include "ds18x20.h"

#include "AppSensorClient.hpp"

namespace app
{
    class AppSensorTemperature
    {
    private:
        AppSensorClient *m_client;
        int m_period;

        static void readTask(void *arg);
        float readTemperature(void);

        gpio_num_t m_sensor_pin{GPIO_NUM_14};
        ds18x20_addr_t m_addr[1];
        bool m_found{0};

        static constexpr const char *TAG{"sensor"};

    public:
        void init(app::AppSensorClient *cl, int period)
        {
            m_client = cl;
            m_period = period * 1000;
            m_found = ds18x20_scan_devices(m_sensor_pin, m_addr, 1) > 0;
            if (!m_found)
            {
                ESP_LOGW(TAG, "sensor not found");
            }
        }

        void start(void)
        {
            xTaskCreate(readTask, TAG, 4096, this, 5, nullptr);
        }
    };

    void AppSensorTemperature::readTask(void *arg)
    {
        AppSensorTemperature *obj = reinterpret_cast<AppSensorTemperature *>(arg);
        while (1)
        {
            vTaskDelay(obj->m_period / portTICK_PERIOD_MS);
            obj->m_client->update(obj->readTemperature());
        }
    }

    float AppSensorTemperature::readTemperature(void)
    {
        float temp{0.0};
        if (m_found)
        {
            ds18x20_measure(m_sensor_pin, m_addr[0], true);
            ds18x20_read_temperature(m_sensor_pin, m_addr[0], &temp);
        }
        return temp;
    }
}