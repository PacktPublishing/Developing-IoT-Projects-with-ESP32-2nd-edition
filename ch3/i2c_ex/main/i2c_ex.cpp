#include "esp_err.h"
#include "esp_log.h"
#include "freertos/FreeRTOS.h"
#include "freertos/task.h"

#include "AppMultisensor.hpp"

extern "C" void app_main(void)
{
    app::AppMultisensor multisensor;
    multisensor.init();

    while (true)
    {
        vTaskDelay(10000 / portTICK_PERIOD_MS);
        auto reading = multisensor.read();
        ESP_LOGI(__func__, "pres: %f, temp: %f, hum: %f, lux: %d",
                 reading.pressure, reading.temperature, reading.humidity, reading.lux);
    }
}
