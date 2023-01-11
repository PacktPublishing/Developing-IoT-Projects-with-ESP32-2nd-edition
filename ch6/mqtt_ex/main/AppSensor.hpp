#pragma once

#include <string>
#include "json.hpp"

namespace app
{
    class AppSensor
    {
    protected:
        std::string m_sensor_name;
        bool m_enabled;
        nlohmann::json m_state;
        virtual void handleNewState(void) = 0;

    public:
        AppSensor(std::string name) : m_sensor_name(name), m_enabled(false)
        {
            m_state["enabled"] = false;
        }
        virtual ~AppSensor() {}

        virtual void init(void) = 0;

        std::string getName(void) const { return m_sensor_name; }
        bool isEnabled(void) const { return m_enabled; }
        
        std::string getState(void) const { return m_state.dump(); }
        void setState(std::string new_state)
        {
            nlohmann::json val = nlohmann::json::parse(new_state, nullptr, false);
            if (!val.is_discarded())
            {
                m_state.merge_patch(val);
                m_enabled = m_state["enabled"].get<bool>();
                handleNewState();
            }
        }
    };
}
