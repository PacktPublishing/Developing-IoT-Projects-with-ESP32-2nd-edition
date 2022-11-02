#pragma once

#include <cinttypes>
#include "esp_err.h"
#include "nvs_flash.h"
#include "nvs.h"

#define NAME_SPACE "app"
#define KEY "settings"

namespace app
{
    class AppSettings
    {
    private:
        uint8_t m_volume;

    public:
        AppSettings() : m_volume(50) {}

        uint8_t getVolume(void) const { return m_volume; }

        void updateVolume(uint8_t vol)
        {
            if (vol == m_volume)
            {
                return;
            }
            nvs_handle_t my_handle{0};
            if (nvs_open(NAME_SPACE, NVS_READWRITE, &my_handle) == ESP_OK)
            {
                m_volume = vol;
                nvs_set_blob(my_handle, KEY, this, sizeof(AppSettings));
                nvs_commit(my_handle);
                nvs_close(my_handle);
            }
        }

        void init(void)
        {
            if (nvs_flash_init() != ESP_OK)
            {
                nvs_flash_erase();
                if (nvs_flash_init() != ESP_OK)
                {
                    return;
                }
            }

            nvs_handle_t my_handle{0};
            if (nvs_open(NAME_SPACE, NVS_READONLY, &my_handle) == ESP_ERR_NVS_NOT_FOUND)
            {
                updateVolume(50);
            }
            else
            {
                size_t len = sizeof(AppSettings);
                if (nvs_get_blob(my_handle, KEY, this, &len) != ESP_OK)
                {
                    updateVolume(50);
                }
            }
            nvs_close(my_handle);
        }
    };

}