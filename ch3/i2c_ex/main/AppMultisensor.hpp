
#pragma once

#include <cstring>
#include "tsl2561.h"
#include "bmp280.h"

namespace app
{
    struct SensorReading
    {
        float pressure;
        float temperature;
        float humidity;
        uint32_t lux;
    };

    class AppMultisensor
    {
    private:
        tsl2561_t m_light_sensor;
        bmp280_t m_temp_sensor;
        bmp280_params_t m_bme280_params;

    public:
        void init(void)
        {
            ESP_ERROR_CHECK(i2cdev_init());

            memset(&m_light_sensor, 0, sizeof(tsl2561_t));
            ESP_ERROR_CHECK(tsl2561_init_desc(&m_light_sensor, TSL2561_I2C_ADDR_FLOAT, I2C_NUM_1, GPIO_NUM_41, GPIO_NUM_40));
            ESP_ERROR_CHECK(tsl2561_init(&m_light_sensor));

            ESP_ERROR_CHECK(bmp280_init_default_params(&m_bme280_params));
            ESP_ERROR_CHECK(bmp280_init_desc(&m_temp_sensor, BMP280_I2C_ADDRESS_0, I2C_NUM_1, GPIO_NUM_41, GPIO_NUM_40));
            ESP_ERROR_CHECK(bmp280_init(&m_temp_sensor, &m_bme280_params));
        }
        SensorReading read(void)
        {
            SensorReading reading;
            bmp280_read_float(&m_temp_sensor, &reading.temperature, &reading.pressure, &reading.humidity);
            tsl2561_read_lux(&m_light_sensor, &reading.lux);
            return reading;
        }
    };
} // namespace app
