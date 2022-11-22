#pragma once

#include "esp_log.h"
#include "bsp_board.h"
#include "bsp_btn.h"
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

        static AppNavigator &getObject(void *btn_ptr)
        {
            button_dev_t *btn_dev = reinterpret_cast<button_dev_t *>(btn_ptr);
            return *(reinterpret_cast<AppNavigator *>(btn_dev->cb_user_data));
        }

        static void countPressed(void *btn_ptr)
        {
            AppNavigator &obj = getObject(btn_ptr);
            obj.m_touch_list = obj.m_touch_logger.serialize();
            obj.m_list_pos = 0;
            ESP_LOGI(TAG, "Touch event count: %u", obj.m_touch_list.size());
        }

        static void nextPressed(void *btn_ptr)
        {
            AppNavigator &obj = getObject(btn_ptr);
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
            bsp_board_init();
            bsp_btn_register_callback(BOARD_BTN_ID_PREV, BUTTON_PRESS_DOWN, AppNavigator::countPressed, reinterpret_cast<void *>(this));
            bsp_btn_register_callback(BOARD_BTN_ID_ENTER, BUTTON_PRESS_DOWN, AppNavigator::nextPressed, reinterpret_cast<void *>(this));

            m_touch_logger.init();
        }
    };
}