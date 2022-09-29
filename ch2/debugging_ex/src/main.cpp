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
        vTaskDelay(1000 / portTICK_RATE_MS);
        ++i;
        my_func();
    }
}