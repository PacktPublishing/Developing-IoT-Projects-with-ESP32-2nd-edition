#pragma once

#include <string>
#include <ctime>
#include <vector>

#include "esp_log.h"
#include "driver/touch_pad.h"
#include "json.hpp"

namespace app
{
    struct AppTouch_t
    {
        uint32_t timestamp;
        uint32_t pad_num;
        uint32_t pad_status;
        uint32_t intr_mask;
    };
    NLOHMANN_DEFINE_TYPE_NON_INTRUSIVE(AppTouch_t, timestamp, pad_num, pad_status, intr_mask);

    class AppTouchLogger
    {
    private:
        constexpr static const char *TAG{"touch_logger"};
        std::vector<AppTouch_t> m_touch_list;

        static void touchsensor_interrupt_cb(void *arg)
        {
            // uint32_t pad_num = touch_pad_get_current_meas_channel();
            // uint32_t pad_status = touch_pad_get_status();
            // uint32_t intr_mask = touch_pad_read_intr_status_mask();
            // if (intr_mask & TOUCH_PAD_INTR_MASK_ACTIVE)
            // {
            // }
            // else
            // {
            // }
            AppTouch_t app_touch{esp_log_timestamp(),
                                 touch_pad_get_current_meas_channel(),
                                 touch_pad_get_status(),
                                 touch_pad_read_intr_status_mask()};

            AppTouchLogger &obj = *(reinterpret_cast<AppTouchLogger *>(arg));
            obj.m_touch_list.push_back(app_touch);
        }

    public:
        void init(void)
        {
            touch_pad_init();
            touch_pad_config(TOUCH_PAD_NUM9);
            touch_pad_isr_register(touchsensor_interrupt_cb, this, TOUCH_PAD_INTR_MASK_ALL);
            touch_pad_intr_enable(TOUCH_PAD_INTR_MASK_ACTIVE | TOUCH_PAD_INTR_MASK_INACTIVE);
        }

        nlohmann::json serialize(void)
        {
            return m_touch_list;
        }
    };
}