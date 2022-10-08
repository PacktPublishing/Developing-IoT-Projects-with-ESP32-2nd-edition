/* Diagnostics Smoke Test Example

   This example code is in the Public Domain (or CC0 licensed, at your option.)

   Unless required by applicable law or agreed to in writing, this
   software is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
   CONDITIONS OF ANY KIND, either express or implied.
*/
#include "string.h"
#include "esp_log.h"
#include "nvs_flash.h"
#include "esp_insights.h"
#include "esp_rmaker_utils.h"
#include "app_wifi.h"
#include "esp_diagnostics_system_metrics.h"
#include "freertos/FreeRTOS.h"
#include "freertos/task.h"


/* The examples uses configuration that you can set via project configuration menu

    If you'd rather not, just change the below entries to strings with
    the config you want - ie #define EXAMPLE_WIFI_SSID "mywifissid"

    Default values:
        CONFIG_ESP_WIFI_SSID               : "myssid"
        CONFIG_ESP_WIFI_PASSWORD           : "mypassword"
*/
#define EXAMPLE_ESP_WIFI_SSID               CONFIG_ESP_WIFI_SSID
#define EXAMPLE_ESP_WIFI_PASS               CONFIG_ESP_WIFI_PASSWORD

#define MAX_CRASHES 5
#define MAX_PTRS    30

static const char *TAG = "diag_smoke";
RTC_NOINIT_ATTR static uint32_t s_reset_count;
static void *s_ptrs[MAX_PTRS];

static void smoke_test(void *arg)
{
    ESP_LOGI(TAG, "In smoke_test");
    int dice;
    int count = 0;
    bool allocating = false;

    while (1) {
        dice = esp_random() % 500;
        ESP_LOGI(TAG, "dice=%d", dice);
        if (dice > 0 && dice < 150) {
            ESP_LOGE(TAG, "[count][%d]", count);
        } else if (dice > 150 && dice < 300) {
            ESP_LOGW(TAG, "[count][%d]", count);
        } else if (dice > 300 && dice < 470) {
            ESP_DIAG_EVENT(TAG, "[count][%d]", count);
        } else {
            /* 30 in 500 probability to crash */
            if (s_reset_count > MAX_CRASHES) {
                ESP_DIAG_EVENT(TAG, "[count][%d]", count);
            } else {
               ESP_LOGE(TAG, "[count][%d] [crash_count][%d] [excvaddr][0x0f] Crashing...", count, s_reset_count);
               *(int *)0x0F = 0x10;
           }
        }

        esp_diag_heap_metrics_dump();
        if (count % MAX_PTRS == 0) {
            allocating = !allocating;
            ets_printf("Allocating:%s\n", allocating ? "true" : "false");
        }
        if (allocating) {
            uint32_t size = 1024 * (esp_random() % 8);
            void *p = malloc(size);
            if (p) {
                memset(p, size, 'A' + (esp_random() % 26));
                ESP_LOGI(TAG, "Allocated %d bytes", size);
            }
            s_ptrs[count % MAX_PTRS] = p;
        } else {
            free(s_ptrs[count % MAX_PTRS]);
            s_ptrs[count % MAX_PTRS] = NULL;
            ESP_LOGI(TAG, "Freeing some memory...");
        }

        count++;
        vTaskDelay(1000);
    }
}

void app_main(void)
{
    /* Initialize NVS */
    esp_err_t ret = nvs_flash_init();
    if (ret == ESP_ERR_NVS_NO_FREE_PAGES || ret == ESP_ERR_NVS_NEW_VERSION_FOUND) {
      ESP_ERROR_CHECK(nvs_flash_erase());
      ret = nvs_flash_init();
    }
    ESP_ERROR_CHECK(ret);

    ret = app_wifi_sta_init(EXAMPLE_ESP_WIFI_SSID, EXAMPLE_ESP_WIFI_PASS);
    if (ret != ESP_OK) {
        ESP_LOGE(TAG, "Failed to connect to Wi-Fi, err:0x%x", ret);
    }
    ESP_ERROR_CHECK(ret);

    /* This initializes SNTP for time synchronization.
     * ESP Insights uses relative time since bootup if time is not synchronized and
     * epoch since 1970 if time is synsynchronized.
     */
    esp_rmaker_time_sync_init(NULL);

    esp_insights_config_t config = {
        .log_type = ESP_DIAG_LOG_TYPE_ERROR | ESP_DIAG_LOG_TYPE_WARNING | ESP_DIAG_LOG_TYPE_EVENT,
    };
    ret = esp_insights_init(&config);
    if (ret != ESP_OK) {
        ESP_LOGE(TAG, "Failed to init ESP Insights, err:0x%x", ret);
    }
    ESP_ERROR_CHECK(ret);

    if (esp_reset_reason() == ESP_RST_POWERON)  {
        s_reset_count = 1;
    } else {
        s_reset_count++;
    }

    xTaskCreate(smoke_test, "smoke_test", (8 * 1024), NULL, 5, NULL);
}
