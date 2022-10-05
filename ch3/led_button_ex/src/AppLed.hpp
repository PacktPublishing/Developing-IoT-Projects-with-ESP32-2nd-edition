#pragma once
#include "driver/gpio.h"

namespace app
{
    class AppLed
    {
    public:
        void init(void)
        {
            gpio_config_t config{GPIO_SEL_39,
                                 GPIO_MODE_OUTPUT,
                                 GPIO_PULLUP_DISABLE,
                                 GPIO_PULLDOWN_DISABLE,
                                 GPIO_INTR_DISABLE};
            gpio_config(&config);
        }
        void set(bool val)
        {
            gpio_set_level(GPIO_NUM_39, static_cast<uint32_t>(val));
        }
    };
}