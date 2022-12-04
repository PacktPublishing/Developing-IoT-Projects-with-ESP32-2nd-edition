#pragma once

#include <mutex>
#include <string>

#include "bsp_lcd.h"
#include "esp_log.h"
#include "freertos/FreeRTOS.h"
#include "freertos/task.h"
#include "lvgl/lvgl.h"
#include "lv_port/lv_port.h"
#include "ui.h"

#include "AppButton.hpp"
#include "AppNav.hpp"
#include "AppAudio.hpp"

namespace
{
    app::AppNav m_nav;

}

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

        static void buttonEventTask(void *param)
        {
            AppUi &ui = *(reinterpret_cast<AppUi *>(param));
            app::eBtnEvent evt;

            while (true)
            {
                xQueueReceive(ui.getButtonEventQueue(), &evt, portMAX_DELAY);
                ui.handleButtonEvent(evt);
            }
        }

        static void audioEventTask(void *param)
        {
            AppUi &ui = *(reinterpret_cast<AppUi *>(param));
            app::eAudioEvent evt;

            while (true)
            {
                xQueueReceive(ui.getAudioEventQueue(), &evt, portMAX_DELAY);
                ui.handleAudioEvent(evt);
            }
        }

        static std::string makeImagePath(const std::string &filename)
        {
            return std::string("S:/spiffs/") + filename;
        }

        static std::string makeAudioPath(const std::string &filename)
        {
            return std::string("/spiffs/") + filename;
        }

        void update(const Animal_t &an, bool play = true)
        {
            ESP_LOGI("ui", "%s", an.animal.c_str());
            lv_label_set_text(ui_txtFilename, an.animal.c_str());
            lv_img_set_src(ui_imgAnimal, makeImagePath(an.image).c_str());
        }

        void toggleControl(void)
        {
            m_playlist_active = !m_playlist_active;
            if (m_playlist_active)
            {
                lv_event_send(ui_btnPlay, LV_EVENT_FOCUSED, nullptr);
            }
            else
            {
                lv_event_send(ui_barVolume, LV_EVENT_FOCUSED, nullptr);
            }
        }

        bool m_playlist_active;
        QueueHandle_t m_evt_queue;
        app::AppAudio *m_app_audio;

    public:
        void init(QueueHandle_t evt_queue, app::AppAudio *audio)
        {
            m_evt_queue = evt_queue;
            m_app_audio = audio;

            lv_port_init();
            ui_init();
            m_nav.init();

            m_playlist_active = true;
            lv_event_send(ui_btnPlay, LV_EVENT_FOCUSED, nullptr);
            update(m_nav.getCurrent(), false);

            bsp_lcd_set_backlight(true);

            xTaskCreatePinnedToCore(lvglTask, "lvgl", 6 * 1024, nullptr, 3, nullptr, 0);
            xTaskCreate(buttonEventTask, "btn_evt", 3 * 1024, this, 3, nullptr);
            xTaskCreate(audioEventTask, "audio_evt", 3 * 1024, this, 3, nullptr);
        }

        QueueHandle_t getButtonEventQueue(void) const { return m_evt_queue; }
        QueueHandle_t getAudioEventQueue(void) const { return m_app_audio->getEventQueue(); }

        void handleButtonEvent(app::eBtnEvent &btn_evt)
        {
            std::lock_guard<std::mutex> lock(m_ui_access);
            switch (btn_evt)
            {
            case app::eBtnEvent::M_DCLICK:
                toggleControl();
                break;
            case app::eBtnEvent::M_CLICK:
                if (m_playlist_active)
                {
                    m_app_audio->togglePlay(makeAudioPath(m_nav.getCurrent().audio));
                }
                else
                {
                }
                break;

            case app::eBtnEvent::L_CLICK:
                if (m_playlist_active)
                {
                    update(m_nav.prev());
                }
                else
                {
                }
                break;
            case app::eBtnEvent::R_CLICK:
                if (m_playlist_active)
                {
                    update(m_nav.next());
                }
                else
                {
                }
                break;

            default:
                break;
            }
        }

        void handleAudioEvent(app::eAudioEvent &evt)
        {
            if (evt == app::eAudioEvent::PLAYING)
            {
                lv_label_set_text(ui_txtPlayButton, "Pause");
            }
            else
            {
                lv_label_set_text(ui_txtPlayButton, "Play");
            }
        }
    };

    std::mutex AppUi::m_ui_access;
}