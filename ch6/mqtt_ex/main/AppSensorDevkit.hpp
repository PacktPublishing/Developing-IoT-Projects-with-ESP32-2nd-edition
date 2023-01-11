#pragma once

#include "AppSensor.hpp"
#include "AppEsp32C3Bsp.hpp"
#include "sdkconfig.h"

namespace app
{
    NLOHMANN_DEFINE_TYPE_NON_INTRUSIVE(BspLed_t, state, hue, saturation, brightness);

    class AppSensorDevkit : public AppSensor
    {
    private:
        AppEsp32C3Bsp m_bsp;
        bool m_toggle_btn;

        static void handleBtn(void *arg)
        {
            AppSensorDevkit *obj = reinterpret_cast<AppSensorDevkit *>(arg);
            obj->m_toggle_btn = !obj->m_toggle_btn;
            obj->m_state["button"] = obj->m_toggle_btn ? "on" : "off";
        }

    protected:
        void handleNewState(void) override
        {
            m_state["button"] = m_toggle_btn ? "on" : "off";
            m_bsp.setLed(m_state["led"]);
            m_state["led"] = m_bsp.getLed();
        }

    public:
        AppSensorDevkit() : AppSensor(CONFIG_MQTT_CLIENT_IDENTIFIER), m_toggle_btn(false)
        {
            m_state = {{"button", "off"},
                       {"led", m_bsp.getLed()}};
        }

        void init(void) override
        {
            m_bsp.init();
            auto fn = [](void *arg)
            {
                handleBtn(arg);
            };
            m_bsp.addButtonHandler(button_cb_type_t::BUTTON_CB_RELEASE, fn, this);
        }
    };
}