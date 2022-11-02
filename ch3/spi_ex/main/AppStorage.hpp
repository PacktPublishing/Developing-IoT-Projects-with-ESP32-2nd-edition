#pragma once

#include <fstream>
#include "esp_err.h"
#include "esp_log.h"
#include "esp_vfs_fat.h"
#include "sdmmc_cmd.h"

namespace app
{
    class AppStorage
    {
    private:
        constexpr static const gpio_num_t PIN_NUM_MOSI{GPIO_NUM_4};
        constexpr static const gpio_num_t PIN_NUM_MISO{GPIO_NUM_6};
        constexpr static const gpio_num_t PIN_NUM_CS{GPIO_NUM_1};
        constexpr static const gpio_num_t PIN_NUM_CLK{GPIO_NUM_5};

        constexpr static const char *MOUNT_POINT{"/sdcard"};

        sdmmc_card_t *m_card;
        spi_host_device_t m_host_slot;

        bool m_sdready;

    public:
        AppStorage() : m_card(nullptr), m_sdready{false}
        {
        }
        virtual ~AppStorage()
        {
            if (m_sdready)
            {
                esp_vfs_fat_sdcard_unmount(MOUNT_POINT, m_card);
                spi_bus_free(m_host_slot);
            }
        }

        esp_err_t init(void)
        {
            esp_err_t ret{ESP_OK};
            esp_vfs_fat_mount_config_t mount_config = {
                .format_if_mount_failed = true,
                .max_files = 5,
                .allocation_unit_size = 16 * 1024};

            spi_bus_config_t bus_cfg = {
                .mosi_io_num = PIN_NUM_MOSI,
                .miso_io_num = PIN_NUM_MISO,
                .sclk_io_num = PIN_NUM_CLK,
                .quadwp_io_num = -1,
                .quadhd_io_num = -1,
                .max_transfer_sz = 4000,
            };

            sdmmc_host_t host = SDSPI_HOST_DEFAULT();

            ret = spi_bus_initialize((spi_host_device_t)host.slot, &bus_cfg, SDSPI_DEFAULT_DMA);
            if (ret != ESP_OK)
            {
                return ret;
            }

            sdspi_device_config_t slot_config = SDSPI_DEVICE_CONFIG_DEFAULT();
            slot_config.gpio_cs = PIN_NUM_CS;
            slot_config.host_id = (spi_host_device_t)host.slot;
            m_host_slot = (spi_host_device_t)host.slot;

            ret = esp_vfs_fat_sdspi_mount(MOUNT_POINT, &host, &slot_config, &mount_config, &m_card);
            if (ret != ESP_OK)
            {
                return ret;
            }
            sdmmc_card_print_info(stdout, m_card);
            m_sdready = true;
            return ret;
        }

        void save(const uint8_t *data, size_t len)
        {
            if (!m_sdready)
            {
                ESP_LOGW(__func__, "sdcard is not ready");
                return;
            }

            std::ofstream file{std::string(MOUNT_POINT) + "/log.bin", std::ios_base::binary | std::ios_base::out | std::ios_base::app};
            if (!file.fail())
            {
                file.write((const char *)data, len);
                if (!file.good())
                {
                    ESP_LOGE(__func__, "file write failed");
                }
            }
            else
            {
                ESP_LOGE(__func__, "file open failed");
            }
        }
    };
}