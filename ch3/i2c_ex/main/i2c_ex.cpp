#include <cstdlib>
#include <cstring>

#include "bsp_i2c.h"
#include "esp_log.h"
#include "esp_err.h"
#include "freertos/FreeRTOS.h"
#include "freertos/task.h"
#include "driver/gpio.h"
#include "driver/i2c.h"

#include "tsl2561.h"
#include "bmp280.h"

namespace
{
    tsl2561_t light_sensor;
    bmp280_t temp_sensor;
}

extern "C" void app_main(void)
{
    ESP_ERROR_CHECK(i2cdev_init());

    memset(&light_sensor, 0, sizeof(tsl2561_t));

    ESP_ERROR_CHECK(tsl2561_init_desc(&light_sensor, TSL2561_I2C_ADDR_FLOAT, I2C_NUM_1, GPIO_NUM_41, GPIO_NUM_40));
    ESP_ERROR_CHECK(tsl2561_init(&light_sensor));

    bmp280_params_t params;
    ESP_ERROR_CHECK(bmp280_init_default_params(&params));

    ESP_ERROR_CHECK(bmp280_init_desc(&temp_sensor, BMP280_I2C_ADDRESS_0, I2C_NUM_1, GPIO_NUM_41, GPIO_NUM_40));
    ESP_ERROR_CHECK(bmp280_init(&temp_sensor, &params));

    float pressure = 0, temperature = 0, humidity = 0;
    uint32_t lux = 0;

    while (1)
    {
        vTaskDelay(10000 / portTICK_PERIOD_MS);
        ESP_ERROR_CHECK(bmp280_read_float(&temp_sensor, &temperature, &pressure, &humidity));
        ESP_ERROR_CHECK(tsl2561_read_lux(&light_sensor, &lux));

        ESP_LOGI(__func__, "pres: %f, temp: %f, hum: %f, lux: %d", pressure, temperature, humidity, lux);
    }
}
