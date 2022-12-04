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
            lv_label_set_text(ui_txtAnimal, an.animal.c_str());
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
        app::AppAudio *m_app_audio;
        app::AppButton *m_app_button;

    public:
        void init(app::AppButton *button, app::AppAudio *audio)
        {
            m_app_button = button;
            m_app_audio = audio;

            lv_port_init();
            ui_init();
            m_nav.init();

            m_playlist_active = true;
            lv_event_send(ui_btnPlay, LV_EVENT_FOCUSED, nullptr);
            lv_bar_set_range(ui_barVolume, 0, 100);
            lv_bar_set_value(ui_barVolume, 50, lv_anim_enable_t::LV_ANIM_OFF);

            update(m_nav.getCurrent(), false);

            bsp_lcd_set_backlight(true);

            xTaskCreatePinnedToCore(lvglTask, "lvgl", 6 * 1024, nullptr, 3, nullptr, 0);
            xTaskCreate(buttonEventTask, "btn_evt", 3 * 1024, this, 3, nullptr);
            xTaskCreate(audioEventTask, "audio_evt", 3 * 1024, this, 3, nullptr);
        }

        QueueHandle_t getButtonEventQueue(void) const { return m_app_button->getEventQueue(); }
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
                    lv_event_send(ui_btnPlay, LV_EVENT_CLICKED, nullptr);
                    m_app_audio->togglePlay(makeAudioPath(m_nav.getCurrent().audio));
                }
                else
                {
                    lv_bar_set_value(ui_barVolume, m_app_audio->mute(false, true), lv_anim_enable_t::LV_ANIM_OFF);
                }
                break;

            case app::eBtnEvent::L_PRESSED:
                if (m_playlist_active)
                {
                    lv_event_send(ui_btnPrev, LV_EVENT_PRESSED, nullptr);
                }
                else
                {
                    lv_event_send(ui_btnVolumeDown, LV_EVENT_PRESSED, nullptr);
                }
                break;
            case app::eBtnEvent::L_RELEASED:
                if (m_playlist_active)
                {
                    lv_event_send(ui_btnPrev, LV_EVENT_RELEASED, nullptr);
                    update(m_nav.prev());
                }
                else
                {
                    lv_event_send(ui_btnVolumeDown, LV_EVENT_RELEASED, nullptr);
                    lv_bar_set_value(ui_barVolume, m_app_audio->volumeDown(), lv_anim_enable_t::LV_ANIM_OFF);
                }
                break;
            case app::eBtnEvent::R_PRESSED:
                if (m_playlist_active)
                {
                    lv_event_send(ui_btnNext, LV_EVENT_PRESSED, nullptr);
                }
                else
                {
                    lv_event_send(ui_btnVolumeUp, LV_EVENT_PRESSED, nullptr);
                }
                break;
            case app::eBtnEvent::R_RELEASED:
                if (m_playlist_active)
                {
                    lv_event_send(ui_btnNext, LV_EVENT_RELEASED, nullptr);
                    update(m_nav.next());
                }
                else
                {
                    lv_event_send(ui_btnVolumeUp, LV_EVENT_RELEASED, nullptr);
                    lv_bar_set_value(ui_barVolume, m_app_audio->volumeUp(), lv_anim_enable_t::LV_ANIM_OFF);
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