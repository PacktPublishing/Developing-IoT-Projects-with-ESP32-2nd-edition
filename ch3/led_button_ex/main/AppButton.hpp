#pragma once
#include <functional>
#include "freertos/FreeRTOS.h"
#include "freertos/task.h"
#include "driver/gpio.h"

namespace
{
    void button_handler(void *arg);
}

namespace app
{
    class AppButton
    {
    private:
        bool state;
        std::function<void(bool)> pressedHandler;

    public:
        AppButton(std::function<void(bool)> h) : state(false), pressedHandler(h) {}

        void init(void)
        {
            gpio_config_t config{(1ull<<38),
                                 GPIO_MODE_INPUT,
                                 GPIO_PULLUP_ENABLE,
                                 GPIO_PULLDOWN_DISABLE,
                                 GPIO_INTR_POSEDGE};
            gpio_config(&config);
            gpio_install_isr_service(0);
            gpio_isr_handler_add(GPIO_NUM_38, button_handler, this);
        }

        void toggle(void)
        {
            state = !state;
            pressedHandler(state);
        }
    };
}

namespace
{
    IRAM_ATTR void button_handler(void *arg)
    {
        static volatile TickType_t next = 0;
        TickType_t now = xTaskGetTickCountFromISR();
        if (now > next)
        {
            auto btn = reinterpret_cast<app::AppButton *>(arg);
            btn->toggle();
            next = now + 500 / portTICK_PERIOD_MS;
        }
    }
}
