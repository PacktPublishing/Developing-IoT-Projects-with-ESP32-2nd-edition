#pragma once

#include <cstdint>

namespace app
{
    typedef struct
    {
        uint8_t light_intensity;
        float temperature;
    } SensorReading_t;
}