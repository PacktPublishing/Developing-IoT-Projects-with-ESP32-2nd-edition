

#include <cinttypes>
#include "esp_log.h"

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
        auto fn = [](const uint8_t *data, size_t len)
        { app_storage.save(data, len); };

        app_sensor.init(fn);
    }
    else
    {
        ESP_LOGE(__func__, "app_storage.init failed");
    }
}
