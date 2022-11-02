#include <stdio.h>
#include <freertos/FreeRTOS.h>
#include <freertos/task.h>
#include <hmc5883l.h>
#include <string.h>

#if defined(CONFIG_IDF_TARGET_ESP8266)
#define SDA_GPIO 4
#define SCL_GPIO 5
#else
#define SDA_GPIO 16
#define SCL_GPIO 17
#endif

#if defined(CONFIG_IDF_TARGET_ESP32S2)
#define APP_CPU_NUM PRO_CPU_NUM
#endif

void hmc5883l_test(void *pvParameters)
{
    hmc5883l_dev_t dev;
    memset(&dev, 0, sizeof(hmc5883l_dev_t));

    ESP_ERROR_CHECK(hmc5883l_init_desc(&dev, 0, SDA_GPIO, SCL_GPIO));
    while (hmc5883l_init(&dev) != ESP_OK)
    {
        printf("HMC5883L not found\n");
        vTaskDelay(250 / portTICK_PERIOD_MS);
    }

    hmc5883l_set_opmode(&dev, HMC5883L_MODE_CONTINUOUS);
    hmc5883l_set_samples_averaged(&dev, HMC5883L_SAMPLES_8);
    hmc5883l_set_data_rate(&dev, HMC5883L_DATA_RATE_07_50);
    hmc5883l_set_gain(&dev, HMC5883L_GAIN_1090);

    while (1)
    {
        hmc5883l_data_t data;
        if (hmc5883l_get_data(&dev, &data) == ESP_OK)
            /* float is used in printf(). you need non-default configuration in
             * sdkconfig for ESP8266, which is enabled by default for this
             * example. see sdkconfig.defaults.esp8266
             */
            printf("Magnetic data: X:%.2f mG, Y:%.2f mG, Z:%.2f mG\n", data.x, data.y, data.z);
        else
            printf("Could not read HMC5883L data\n");

        vTaskDelay(250 / portTICK_PERIOD_MS);
    }
}

void app_main()
{
    ESP_ERROR_CHECK(i2cdev_init());
    xTaskCreatePinnedToCore(hmc5883l_test, "hmc5883l_test", configMINIMAL_STACK_SIZE * 3, NULL, 5, NULL, APP_CPU_NUM);
}

