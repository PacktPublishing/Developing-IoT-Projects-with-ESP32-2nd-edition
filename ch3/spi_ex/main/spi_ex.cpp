

#include <cinttypes>

#include "freertos/FreeRTOS.h"
#include "freertos/task.h"

#include "AppStorage.hpp"
#include "AppSensor.hpp"

namespace
{
    app::AppStorage app_storage;
    app::AppSensor app_sensor;
}

extern "C" void app_main(void)
{
    if (app_storage.init() == ESP_OK)
    {
        app_sensor.init([](const uint8_t *data, size_t len)
                        { app_storage.save(data, len); });
    }
    else
    {
        ESP_LOGE(__func__, "app_storage.init failed");
    }
}
