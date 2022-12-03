#pragma once

#include <mutex>
#include <vector>

#include "bsp_lcd.h"
#include "esp_log.h"
#include "freertos/FreeRTOS.h"
#include "freertos/task.h"
#include "lvgl/lvgl.h"
#include "lv_port/lv_port.h"
#include "ui.h"

#include "AppButton.hpp"
#include "AppNav.hpp"

namespace app
{
    class AppUi
    {
    private:
        static std::mutex m_ui_access;
        static void lvglTask(void *param)
        {
            while (true)
            {
                {
                    std::lock_guard<std::mutex> lock(m_ui_access);
                    lv_task_handler();
                }
                vTaskDelay(pdMS_TO_TICKS(10));
            }
        }

        static void btnTask(void *param)
        {
            AppUi &ui = *(reinterpret_cast<AppUi *>(param));
            app::eBtnEvent evt;

            while (true)
            {
                xQueueReceive(ui.getEventQueue(), &evt, portMAX_DELAY);
                ui.handleButtonEvent(evt);
            }
        }

        bool m_playlist_active;
        QueueHandle_t m_evt_queue;
        AppNav m_nav;

    public:
        void init(QueueHandle_t evt_queue)
        {
            m_evt_queue = evt_queue;

            lv_port_init();
            ui_init();
            m_nav.init();

            m_playlist_active = true;
            lv_event_send(ui_btnPlay, LV_EVENT_FOCUSED, nullptr);
            lv_img_set_src(ui_imgAnimal, "S:/spiffs/dog.png");
            bsp_lcd_set_backlight(true);

            xTaskCreatePinnedToCore(lvglTask, "lvgl", 6 * 1024, nullptr, 3, nullptr, 0);
            xTaskCreate(btnTask, "btn", 2 * 1024, this, 3, nullptr);
        }

        QueueHandle_t getEventQueue(void) const { return m_evt_queue; }

        void handleButtonEvent(app::eBtnEvent &btn_evt)
        {
            std::lock_guard<std::mutex> lock(m_ui_access);
            switch (btn_evt)
            {
            case app::eBtnEvent::M_DCLICK:
                m_playlist_active = !m_playlist_active;
                if (m_playlist_active)
                {
                    lv_event_send(ui_btnPlay, LV_EVENT_FOCUSED, nullptr);
                }
                else
                {
                    lv_event_send(ui_barVolume, LV_EVENT_FOCUSED, nullptr);
                }
                break;
            case app::eBtnEvent::M_CLICK:
                if (m_playlist_active)
                {
                    Animal_t &an = m_nav.getCurrent();
                    ESP_LOGI("ui", "%s", an.animal.c_str());
                    lv_label_set_text(ui_txtFilename, an.animal.c_str());
                }
                else
                {
                }
                break;

            case app::eBtnEvent::L_CLICK:
                if (m_playlist_active)
                {
                    Animal_t &an = m_nav.prev();
                    ESP_LOGI("ui", "%s", an.animal.c_str());
                    lv_label_set_text(ui_txtFilename, an.animal.c_str());
                }
                else
                {
                }
                break;
            case app::eBtnEvent::R_CLICK:
                if (m_playlist_active)
                {
                    Animal_t &an = m_nav.next();
                    ESP_LOGI("ui", "%s", an.animal.c_str());
                    lv_label_set_text(ui_txtFilename, an.animal.c_str());
                }
                else
                {
                }
                break;

            default:
                break;
            }
        }
    };

    std::mutex AppUi::m_ui_access;
}