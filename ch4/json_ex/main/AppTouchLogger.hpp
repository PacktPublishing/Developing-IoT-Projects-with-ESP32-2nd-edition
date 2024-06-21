#pragma once

#include <string>
#include <ctime>
#include <vector>

#include "freertos/FreeRTOS.h"
#include "freertos/task.h"
#include "esp_log.h"
#include "driver/touch_pad.h"
#include "json.hpp"

namespace app
{
    struct TouchEvent_t
    {
        uint32_t timestamp;
        uint32_t pad_num;
        uint32_t intr_mask;
    };
    NLOHMANN_DEFINE_TYPE_NON_INTRUSIVE(TouchEvent_t, timestamp, pad_num, intr_mask);

    class AppTouchLogger
    {
    private:
        constexpr static const char *TAG{"touch_logger"};
        std::vector<TouchEvent_t> m_touch_list;

        static void touchsensor_interrupt_cb(void *arg)
        {
            TouchEvent_t touch_event{esp_log_timestamp(),
                                     touch_pad_get_current_meas_channel(),
                                     touch_pad_read_intr_status_mask()};

            AppTouchLogger &obj = *(reinterpret_cast<AppTouchLogger *>(arg));
            obj.m_touch_list.push_back(touch_event);
        }

    public:
        void init(void)
        {
            touch_pad_init();
            touch_pad_config(TOUCH_PAD_NUM9);

            touch_filter_config_t filter_info = {
                .mode = TOUCH_PAD_FILTER_IIR_16,
                .debounce_cnt = 1,
                .noise_thr = 0,
                .jitter_step = 4,
                .smh_lvl = TOUCH_PAD_SMOOTH_IIR_2,
            };
            touch_pad_filter_set_config(&filter_info);
            touch_pad_filter_enable();
            touch_pad_timeout_set(true, SOC_TOUCH_PAD_THRESHOLD_MAX);

            touch_pad_isr_register(touchsensor_interrupt_cb, this, static_cast<touch_pad_intr_mask_t>(TOUCH_PAD_INTR_MASK_ALL));
            touch_pad_intr_enable(static_cast<touch_pad_intr_mask_t>(TOUCH_PAD_INTR_MASK_ACTIVE | TOUCH_PAD_INTR_MASK_INACTIVE));

            touch_pad_set_fsm_mode(TOUCH_FSM_MODE_TIMER);
            touch_pad_fsm_start();

            vTaskDelay(pdMS_TO_TICKS(50));
            uint32_t touch_value;
            touch_pad_read_benchmark(TOUCH_PAD_NUM9, &touch_value);
            touch_pad_set_thresh(TOUCH_PAD_NUM9, touch_value * .2);
        }

        nlohmann::json serialize(void)
        {
            return m_touch_list;
        }
    };
}