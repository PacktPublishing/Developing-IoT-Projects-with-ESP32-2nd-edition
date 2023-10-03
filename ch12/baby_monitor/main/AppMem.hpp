#pragma once

#include "esp_timer.h"
#include "esp_log.h"
#include "esp_err.h"
#include "esp_heap_caps.h"

namespace app
{
    class AppMem
    {
    private:
        constexpr static const char *TAG{"app-mem"};
        esp_timer_handle_t m_periodic_timer;

        static void periodic_timer_callback(void *arg)
        {
            ESP_LOGI(TAG, "------- mem stats -------");
            ESP_LOGI(TAG, "internal\t: %10u (free) / %10u (total)", heap_caps_get_free_size(MALLOC_CAP_INTERNAL), heap_caps_get_total_size(MALLOC_CAP_INTERNAL));
            ESP_LOGI(TAG, "spiram\t: %10u (free) / %10u (total)", heap_caps_get_free_size(MALLOC_CAP_SPIRAM), heap_caps_get_total_size(MALLOC_CAP_SPIRAM));
        }

    public:
        void monitor(void)
        {
            const esp_timer_create_args_t periodic_timer_args = {
                periodic_timer_callback,
                this};

            ESP_ERROR_CHECK(esp_timer_create(&periodic_timer_args, &m_periodic_timer));
            ESP_ERROR_CHECK(esp_timer_start_periodic(m_periodic_timer, 5000000u));
        }

        void print(void)
        {
            periodic_timer_callback(nullptr);
        }
    };
}
