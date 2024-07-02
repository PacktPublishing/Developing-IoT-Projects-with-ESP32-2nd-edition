#pragma once

#include "esp_log.h"
#include "bsp_board.h"
#include "AppTouchLogger.hpp"
#include "json.hpp"

namespace app
{
    class AppNavigator
    {
    private:
        constexpr static const char *TAG{"nav"};
        AppTouchLogger m_touch_logger;
        nlohmann::json m_touch_list;
        size_t m_list_pos{0};

        static void countPressed(void *btn_ptr, void *user_data)
        {
            AppNavigator &obj = *(reinterpret_cast<AppNavigator *>(user_data));
            obj.m_touch_list = obj.m_touch_logger.serialize();
            obj.m_list_pos = 0;
            ESP_LOGI(TAG, "Touch event count: %u", obj.m_touch_list.size());
        }

        static void nextPressed(void *btn_ptr, void *user_data)
        {
            AppNavigator &obj = *(reinterpret_cast<AppNavigator *>(user_data));
            if (obj.m_touch_list.size() <= 0)
            {
                ESP_LOGW(TAG, "no touch detected");
                return;
            }
            ESP_LOGI(TAG, "%s", obj.m_touch_list[obj.m_list_pos].dump().c_str());
            ++obj.m_list_pos;
            obj.m_list_pos %= obj.m_touch_list.size();
        }

    public:
        void init(void)
        {
            bsp_i2c_init();
            bsp_board_init();
            bsp_btn_register_callback(BOARD_BTN_ID_PREV, BUTTON_PRESS_DOWN, AppNavigator::countPressed, this);
            bsp_btn_register_callback(BOARD_BTN_ID_ENTER, BUTTON_PRESS_DOWN, AppNavigator::nextPressed, this);

            m_touch_logger.init();
        }
    };
}