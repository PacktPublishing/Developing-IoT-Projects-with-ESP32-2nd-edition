#pragma once

#include <mutex>
#include <vector>
#include <ctime>

#include "freertos/FreeRTOS.h"
#include "freertos/task.h"
#include "freertos/timers.h"
#include "freertos/queue.h"
#include "esp_log.h"

#include "bsp_board.h"
#include "bsp_lcd.h"
#include "lvgl/lvgl.h"
#include "lv_port/lv_port.h"
#include "ui.h"
#include "AppCommon.hpp"

namespace app
{
    class AppUi
    {
    private:
        static std::mutex m_ui_access;
        QueueHandle_t m_sensor_reading_queue;

        static void lvglTask(void *arg);
        void setSensorValues(const SensorReading_t &r);
        static void updateDatetime(void *arg);

    public:
        void init(void)
        {
            m_sensor_reading_queue = xQueueCreate(1, sizeof(SensorReading_t));

            bsp_board_init();
            lv_port_init();
            ui_init();
            xTaskCreatePinnedToCore(lvglTask, "lvgl", 6 * 1024, this, 3, nullptr, 0);

            bsp_lcd_set_backlight(true);

            setenv("TZ", "GMT", 1);
            tzset();
        }

        void updateSensorReading(const SensorReading_t &reading)
        {
            xQueueSendToBack(m_sensor_reading_queue, &reading, 0);
        }

        void updateMqttState(bool connected)
        {
            std::lock_guard<std::mutex> lock(m_ui_access);
            if (connected)
            {
                lv_obj_add_state(ui_chkConnected, LV_STATE_CHECKED);
                lv_checkbox_set_text(ui_chkConnected, "Connected");
            }
            else
            {
                lv_checkbox_set_text(ui_chkConnected, "Disconnected");
                lv_obj_clear_state(ui_chkConnected, LV_STATE_CHECKED);
            }
        }

        void start(void)
        {
            static TimerHandle_t timer{nullptr};

            if (timer == nullptr)
            {
                timer = xTimerCreate("datetime", pdMS_TO_TICKS(1000), pdTRUE, nullptr, updateDatetime);
                xTimerStart(timer, 0);
            }
        }
    };

    std::mutex AppUi::m_ui_access;

    void AppUi::setSensorValues(const SensorReading_t &r)
    {
        lv_label_set_text(ui_txtLight, std::to_string(r.light_intensity).c_str());
        lv_label_set_text(ui_txtTemp, std::to_string(r.temperature).substr(0, 4).c_str());
    }

    void AppUi::updateDatetime(void *arg)
    {
        std::lock_guard<std::mutex> lock(m_ui_access);

        time_t now;
        char strftime_buf[64]{0};
        struct tm timeinfo;
        time(&now);
        localtime_r(&now, &timeinfo);
        strftime(strftime_buf, sizeof(strftime_buf), "%c", &timeinfo);
        lv_label_set_text(ui_txtTime, strftime_buf);
    }

    void AppUi::lvglTask(void *arg)
    {
        AppUi *obj = reinterpret_cast<AppUi *>(arg);

        while (true)
        {
            {
                std::lock_guard<std::mutex> lock(m_ui_access);
                SensorReading_t r;
                if (xQueueReceive(obj->m_sensor_reading_queue, &r, 0) == pdTRUE)
                {
                    obj->setSensorValues(r);
                }
                lv_task_handler();
            }
            vTaskDelay(pdMS_TO_TICKS(10));
        }
    }
}