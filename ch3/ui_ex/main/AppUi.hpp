#pragma once

#include <sys/time.h>
#include <mutex>

#include "freertos/FreeRTOS.h"
#include "freertos/task.h"
#include "freertos/semphr.h"
#include "lvgl/lvgl.h"

namespace app
{
    class AppUi
    {
    public:
        void init(void)
        {
            while (true)
            {
                {
                    std::lock_guard<std::mutex> lock(m_ui_access);
                    lv_task_handler();
                }
                vTaskDelay(pdMS_TO_TICKS(10));
            }
            vTaskDelete(NULL);
        }

    private:
        std::mutex m_ui_access;
    };
}