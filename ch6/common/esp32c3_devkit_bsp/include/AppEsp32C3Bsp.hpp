#pragma once

#include <cinttypes>
#include <functional>
#include <map>
#include <vector>

#include "iot_button.h"
#include "led_strip.h"
#include "ws2812_led.h"

namespace app
{
    using BspButtonCb_f = std::function<void(void *)>;

    typedef struct
    {
        BspButtonCb_f fn;
        void *arg;
    } BspButtonHandler_t;

    typedef struct
    {
        bool state;         // off/on
        uint16_t hue;       // 0-360
        uint8_t saturation; // 0-100
        uint8_t brightness; // 0-100
    } BspLed_t;

    class AppEsp32C3Bsp
    {
    private:
        BspLed_t m_led;
        button_handle_t m_btn;
        std::map<button_cb_type_t, std::vector<BspButtonHandler_t>> m_btn_handlers;

        static void handleButtonPush(void *arg)
        {
            AppEsp32C3Bsp *devkit = reinterpret_cast<AppEsp32C3Bsp *>(arg);
            for (auto &handler : devkit->m_btn_handlers[button_cb_type_t::BUTTON_CB_PUSH])
            {
                (handler.fn)(handler.arg);
            }
        }

        static void handleButtonRelease(void *arg)
        {
            AppEsp32C3Bsp *devkit = reinterpret_cast<AppEsp32C3Bsp *>(arg);
            for (auto &handler : devkit->m_btn_handlers[button_cb_type_t::BUTTON_CB_RELEASE])
            {
                (handler.fn)(handler.arg);
            }
        }

    public:
        void init(void)
        {
            ws2812_led_init();
            ws2812_led_clear();
            button_handle_t m_btn = iot_button_create(GPIO_NUM_9, button_active_t::BUTTON_ACTIVE_LOW);
            iot_button_set_evt_cb(m_btn, button_cb_type_t::BUTTON_CB_PUSH, handleButtonPush, this);
            iot_button_set_evt_cb(m_btn, button_cb_type_t::BUTTON_CB_RELEASE, handleButtonRelease, this);
        }

        void addButtonHandler(button_cb_type_t cb_type, BspButtonCb_f btn_cb, void *arg)
        {
            if (cb_type == button_cb_type_t::BUTTON_CB_PUSH || cb_type == button_cb_type_t::BUTTON_CB_RELEASE)
            {
                if (btn_cb != nullptr)
                {
                    m_btn_handlers[cb_type].push_back({btn_cb, arg});
                }
            }
        }

        void setLed(BspLed_t led)
        {
            m_led.hue = led.hue > 360 ? 360 : led.hue;
            m_led.saturation = led.saturation > 100 ? 100 : led.saturation;
            m_led.brightness = led.brightness > 100 ? 100 : led.brightness;
            m_led.state = led.state;
            if (m_led.state)
            {
                ws2812_led_set_hsv(m_led.hue, m_led.saturation, m_led.brightness);
            }
            else
            {
                ws2812_led_clear();
            }
        }

        BspLed_t getLed(void) const { return m_led; }
    };
}