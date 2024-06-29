#pragma once

#include <cstdint>
#include "app_led.h"

#define APP_RED_PIN gpio_num_t::GPIO_NUM_13
#define APP_GREEN_PIN gpio_num_t::GPIO_NUM_12
#define APP_BLUE_PIN gpio_num_t::GPIO_NUM_11

#define RED(x) (uint8_t)(((x)&0xff0000) >> 16)
#define GREEN(x) (uint8_t)(((x)&0x00ff00) >> 8)
#define BLUE(x) (uint8_t)((x)&0x0000ff)

namespace app
{
    enum eColor : uint32_t
    {
        White = 0xffffff,
        Red = 0xff0000,
        Lime = 0x00ff00,
        Blue = 0x0000ff,
        Yellow = 0xffff00,
        Cyan = 0x00ffff,
        Magenta = 0xff00ff,
        Green = 0x008000,
        Purple = 0x800080,
        Navy = 0x000080
    };

    class AppLed
    {
    public:
        void setColor(eColor color)
        {
            app_pwm_led_set_all(RED(color), GREEN(color), BLUE(color));
        }

        void on()
        {
            app_pwm_led_set_power(true);
        }

        void off()
        {
            app_pwm_led_set_power(false);
        }

        void init(void)
        {
            app_pwm_led_init(APP_RED_PIN, APP_GREEN_PIN, APP_BLUE_PIN);
            on();
            setColor(eColor::White);
        }
    };
}
