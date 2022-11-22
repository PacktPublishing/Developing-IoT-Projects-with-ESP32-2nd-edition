#pragma once

#include <cinttypes>
#include "esp_log.h"
#include "flatbuffers/idl.h"
#include "flatbuffers/util.h"
#include "app_data_generated.h"

namespace app
{
    class AppLdrClient
    {
    private:
        LightSensorFbT m_light_sensor;

    public:
        void consume(const uint8_t *buffer)
        {
            app::GetLightSensorFb(buffer)->UnPackTo(&m_light_sensor);
            ESP_LOGI(__func__, "location: %s", m_light_sensor.location.c_str());
            for (auto &&rec : m_light_sensor.readings)
            {
                ESP_LOGI(__func__, "ts: %u, light: %d", rec->timestamp, rec->light);
            }
        }
    };
}
