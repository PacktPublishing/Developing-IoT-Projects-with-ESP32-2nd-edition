// https://github.com/micropython/micropython/issues/7772
// https://docs.espressif.com/projects/esp-idf/en/latest/esp32s3/api-reference/peripherals/i2c.html
// esp32-s3 i2c: i2c_set_timeout(817): i2c timing value error


#include <cstdlib>
#include <cstring>

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

extern "C" void app_main()
{
    // i2c_config_t cfg;
    i2cdev_init();

    memset(&light_sensor, 0, sizeof(tsl2561_t));
    light_sensor.i2c_dev.timeout_ticks = 0xffff / portTICK_PERIOD_MS;

    // tsl2561_init_desc(&light_sensor, TSL2561_I2C_ADDR_FLOAT, 0, GPIO_NUM_21, GPIO_NUM_22);
    tsl2561_init_desc(&light_sensor, TSL2561_I2C_ADDR_FLOAT, 0, GPIO_NUM_41, GPIO_NUM_40);
    tsl2561_init(&light_sensor);

    memset(&temp_sensor, 0, sizeof(bmp280_t));
    temp_sensor.i2c_dev.timeout_ticks = 0xffff / portTICK_PERIOD_MS;

    bmp280_params_t params;
    bmp280_init_default_params(&params);

    bmp280_init_desc(&temp_sensor, BMP280_I2C_ADDRESS_0, 0, GPIO_NUM_41, GPIO_NUM_40);
    // bmp280_init_desc(&temp_sensor, BMP280_I2C_ADDRESS_0, 0, GPIO_NUM_21, GPIO_NUM_22);
    bmp280_init(&temp_sensor, &params);

    float pressure = 0, temperature = 0, humidity = 0;
    uint32_t lux;

    while (1)
    {
        vTaskDelay(10000 / portTICK_PERIOD_MS);
        ESP_ERROR_CHECK(bmp280_read_float(&temp_sensor, &temperature, &pressure, &humidity));
        ESP_ERROR_CHECK(tsl2561_read_lux(&light_sensor, &lux));

        ESP_LOGI(__func__, "pres: %f, temp: %f, hum: %f, lux: %d", pressure, temperature, humidity, lux);
    }
}