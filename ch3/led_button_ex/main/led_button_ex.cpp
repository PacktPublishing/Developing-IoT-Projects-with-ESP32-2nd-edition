#include "freertos/FreeRTOS.h"
#include "freertos/task.h"

#include "AppLed.hpp"
#include "AppButton.hpp"

extern "C" void app_main()
{
    app::AppLed led;
    auto fn = [&led](bool state)
    { led.set(state); };
    app::AppButton button(fn);

    led.init();
    button.init();

    vTaskSuspend(nullptr);
}