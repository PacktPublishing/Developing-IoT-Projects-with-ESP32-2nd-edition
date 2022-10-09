
#pragma once

#include <cinttypes>
#include "esp_err.h"
#include "esp_log.h"
#include "nvs_flash.h"
#include "nvs.h"

#define NAME_SPACE "sys_param"
#define KEY "param"

namespace app
{
    class cAppSettings
    {
    private:
        uint8_t m_volume; // 0 - 100%
    public:
        cAppSettings() : m_volume(50) {}
        void init(void)
        {
            esp_err_t err = nvs_flash_init();
            if (err == ESP_ERR_NVS_NO_FREE_PAGES || err == ESP_ERR_NVS_NEW_VERSION_FOUND)
            {
                ESP_ERROR_CHECK(nvs_flash_erase());
                err = nvs_flash_init();
            }

            nvs_handle_t my_handle = 0;
            esp_err_t ret = nvs_open(NAME_SPACE, NVS_READONLY, &my_handle);
            if (ESP_ERR_NVS_NOT_FOUND == ret)
            {
                ESP_LOGW(__func__, "settings not found.");
                updateVolume(50);
            }
            size_t len = sizeof(cAppSettings);
            ret = nvs_get_blob(my_handle, KEY, this, &len);
            if (ret != ESP_OK)
            {
                updateVolume(50);
                ESP_LOGW(__func__, "nvs read failed");
            }
            nvs_close(my_handle);
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
            nvs_handle_t my_handle = {0};
            esp_err_t err = nvs_open(NAME_SPACE, NVS_READWRITE, &my_handle);
            if (err != ESP_OK)
            {
                ESP_LOGI(__func__, "Error (%s) opening NVS handle!\n", esp_err_to_name(err));
            }
            else
            {
                m_volume = vol;
                err = nvs_set_blob(my_handle, KEY, this, sizeof(cAppSettings));
                err |= nvs_commit(my_handle);
                nvs_close(my_handle);
            }
            return err;
        }
    };

}