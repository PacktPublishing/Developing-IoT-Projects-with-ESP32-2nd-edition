#pragma once

#include <cinttypes>
#include <functional>
#include "freertos/FreeRTOS.h"
#include "freertos/task.h"
#include "esp_log.h"

namespace app
{
    struct SensorData
    {
        int temperature;
        int humidity;
        int pressure;
        int lux;
    };

    class AppSensor
    {
    private:
        SensorData readings[100];
        int cnt = 0;
        std::function<void(const uint8_t *, size_t)> save;

        static void read(void *arg)
        {
            AppSensor *sensor = reinterpret_cast<AppSensor *>(arg);
            while (1)
            {
                vTaskDelay(pdMS_TO_TICKS(100));
                SensorData d{20, 50, 1000, 55};
                sensor->readings[sensor->cnt++] = d;

                if (sensor->cnt == 100)
                {
                    sensor->save(reinterpret_cast<const uint8_t *>(sensor->readings), 100 * sizeof(SensorData));
                    sensor->cnt = 0;
                }
            }
        }

    public:
        void init(std::function<void(const uint8_t *, size_t)> fn)
        {
            save = fn;
            if (xTaskCreate(AppSensor::read,
                            "sensor",
                            3072,
                            reinterpret_cast<void *>(this),
                            5,
                            nullptr) == pdPASS)
            {
                ESP_LOGI(__func__, "task created");
            }
        }
    };
}
