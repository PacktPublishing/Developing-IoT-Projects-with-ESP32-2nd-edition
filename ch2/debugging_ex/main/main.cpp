#include "freertos/FreeRTOS.h"
#include "freertos/task.h"

void my_func(void)
{
    int j = 0;
    ++j;
}

extern "C" void app_main()
{
    int i = 0;
    while (1)
    {
        vTaskDelay(pdMS_TO_TICKS(1000));
        ++i;
        my_func();
    }
}