#pragma once

#include <fstream>
#include <string>
#include <vector>
#include "json.hpp"

namespace app
{
    struct Animal_t
    {
        std::string animal;
        std::string audio;
        std::string image;
    };
    NLOHMANN_DEFINE_TYPE_NON_INTRUSIVE(Animal_t, animal, audio, image);

    class AppNav
    {
    private:
        int m_pos;
        std::vector<Animal_t> m_animals;

    public:
        void init()
        {
            std::ifstream fs{"/spiffs/info.json"};
            m_animals = nlohmann::json::parse(fs);
            m_pos = 0;
        }

        Animal_t &getCurrent(void)
        {
            return m_animals[m_pos];
        }

        Animal_t &next(void)
        {
            m_pos = (m_pos + 1) % m_animals.size();
            return m_animals[m_pos];
        }

        Animal_t &prev(void)
        {
            m_pos = (m_pos - 1) % m_animals.size();
            return m_animals[m_pos];
        }
    };
}