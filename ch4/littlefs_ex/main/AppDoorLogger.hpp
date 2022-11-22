#pragma once

#include <fstream>
#include <string>
#include <ctime>

#include "esp_log.h"
#include "bsp_board.h"
#include "bsp_btn.h"
#include "esp_littlefs.h"

namespace app
{
    class AppDoorLogger
    {
    private:
        constexpr static const char *TAG{"door_logger"};
        constexpr static const char *FILENAME{"/files/log.txt"};

        enum class eDoorState
        {
            OPENED,
            CLOSED
        };
        eDoorState m_door_state;

        static AppDoorLogger &getObject(void *btn_ptr)
        {
            button_dev_t *btn_dev = reinterpret_cast<button_dev_t *>(btn_ptr);
            return *(reinterpret_cast<AppDoorLogger *>(btn_dev->cb_user_data));
        }

        static void doorOpened(void *btn_ptr)
        {
            AppDoorLogger &obj = getObject(btn_ptr);
            obj.m_door_state = eDoorState::OPENED;
            obj.log();
        }

        static void doorClosed(void *btn_ptr)
        {
            AppDoorLogger &obj = getObject(btn_ptr);
            obj.m_door_state = eDoorState::CLOSED;
            obj.log();
        }

        void log(void)
        {
            std::ofstream log_file{FILENAME, std::ios_base::app};
            log_file << "[" << esp_log_system_timestamp() << "]: ";
            log_file << (m_door_state == eDoorState::OPENED ? "opened" : "closed") << "\n";
        }

        static void print(void *data)
        {
            std::ifstream log_file{FILENAME};
            std::string line1;
            while (!log_file.eof())
            {
                std::getline(log_file, line1);
                ESP_LOGI(TAG, "%s", line1.c_str());
            }
        }

    public:
        void init(void)
        {
            bsp_board_init();
            bsp_btn_register_callback(BOARD_BTN_ID_PREV, BUTTON_PRESS_DOWN, AppDoorLogger::doorOpened, reinterpret_cast<void *>(this));
            bsp_btn_register_callback(BOARD_BTN_ID_PREV, BUTTON_PRESS_UP, AppDoorLogger::doorClosed, reinterpret_cast<void *>(this));
            bsp_btn_register_callback(BOARD_BTN_ID_ENTER, BUTTON_PRESS_DOWN, AppDoorLogger::print, nullptr);

            esp_vfs_littlefs_conf_t conf = {
                .base_path = "/files",
                .partition_label = "storage",
                .format_if_mount_failed = true,
                .dont_mount = false,
            };
            esp_vfs_littlefs_register(&conf);

            std::ofstream log_file{FILENAME, std::ios_base::trunc};
            if (!log_file.is_open())
            {
                ESP_LOGE(TAG, "file open failed (%s)", FILENAME);
            }
        }
    };
}