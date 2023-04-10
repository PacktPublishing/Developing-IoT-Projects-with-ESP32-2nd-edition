
#pragma once

namespace app
{
    class AppSensorClient
    {
    public:
        virtual void update(float temperature) = 0;
    };
}