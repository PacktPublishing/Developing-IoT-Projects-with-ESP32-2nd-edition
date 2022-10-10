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
        esp_err_t init(void)
        {
            esp_err_t err = nvs_flash_init();
            if (err == ESP_ERR_NVS_NO_FREE_PAGES || err == ESP_ERR_NVS_NEW_VERSION_FOUND)
            {
                nvs_flash_erase();
                err = nvs_flash_init();
                if (err != ESP_OK)
                {
                    return err;
                }
            }

            nvs_handle_t my_handle{0};
            err = nvs_open(NAME_SPACE, NVS_READONLY, &my_handle);
            if (err == ESP_ERR_NVS_NOT_FOUND)
            {
                err = updateVolume(50);
            }
            else
            {
                size_t len = sizeof(AppSettings);
                err = nvs_get_blob(my_handle, KEY, this, &len);
                if (err != ESP_OK)
                {
                    err = updateVolume(50);
                }
            }
            nvs_close(my_handle);
            return err;
        }

        uint8_t getVolume(void) const
        {
            return m_volume;
        }

        esp_err_t updateVolume(uint8_t vol)
        {
            if (vol == m_volume)
            {
                return ESP_OK;
            }
            nvs_handle_t my_handle{0};
            esp_err_t err = nvs_open(NAME_SPACE, NVS_READWRITE, &my_handle);
            if (err == ESP_OK)
            {
                m_volume = vol;
                err = nvs_set_blob(my_handle, KEY, this, sizeof(AppSettings));
                err |= nvs_commit(my_handle);
                nvs_close(my_handle);
            }
            return err;
        }
    };

}