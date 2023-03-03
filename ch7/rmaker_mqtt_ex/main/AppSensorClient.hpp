
#pragma once
#include <cinttypes>

namespace app
{
    class AppSensorClient
    {
    public:
        virtual void update(uint32_t light_level) = 0;
    };
}