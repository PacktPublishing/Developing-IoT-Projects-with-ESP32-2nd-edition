#pragma once

#include "AppSensor.hpp"

namespace app
{
    class AppSensorDummy : public AppSensor
    {
    protected:
        void handleNewState(void) override
        {
        }

    public:
        AppSensorDummy() : AppSensor("dummy-0")
        {
        }

        void init(void) override
        {
            m_state["dummy_state"] = "on";
        }
    };
}