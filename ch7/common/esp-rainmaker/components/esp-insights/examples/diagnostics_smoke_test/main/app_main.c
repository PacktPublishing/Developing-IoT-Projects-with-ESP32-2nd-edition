/* Diagnostics Smoke Test Example

   This example code is in the Public Domain (or CC0 licensed, at your option.)

   Unless required by applicable law or agreed to in writing, this
   software is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
   CONDITIONS OF ANY KIND, either express or implied.
*/
#include "string.h"
#include "esp_log.h"
#include "esp_netif.h"
#include "esp_event.h"
#include "nvs_flash.h"
#include "protocol_examples_common.h"

#include "esp_insights.h"
#include "esp_rmaker_utils.h"
#include "esp_wifi.h"
#include "esp_diagnostics_system_metrics.h"
#include "freertos/FreeRTOS.h"
#include "freertos/task.h"

/* Note: Wi-Fi station credentials can be changed using CONFIG_EXAMPLE_WIFI_SSID and CONFIG_EXAMPLE_WIFI_PASSWORD */

#define MAX_CRASHES 5
#define MAX_PTRS    30

#ifdef CONFIG_ESP_INSIGHTS_TRANSPORT_HTTPS
extern const char insights_auth_key_start[] asm("_binary_insights_auth_key_txt_start");
extern const char insights_auth_key_end[] asm("_binary_insights_auth_key_txt_end");
#endif

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
        if (count == 5) {
            esp_wifi_disconnect();
        }
        if (count == 8) {
            esp_wifi_connect();
        }
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
               ESP_LOGE(TAG, "[count][%d] [crash_count][%" PRIu32 "] [excvaddr][0x0f] Crashing...", count, s_reset_count);
               *(int *)0x0F = 0x10;
           }
        }

        esp_diag_heap_metrics_dump();
        if (count % MAX_PTRS == 0) {
            allocating = !allocating;
            ESP_LOGI(TAG, "Allocating:%s\n", allocating ? "true" : "false");
        }
        if (allocating) {
            uint32_t size = 1024 * (esp_random() % 8);
            void *p = malloc(size);
            if (p) {
                memset(p, size, 'A' + (esp_random() % 26));
                ESP_LOGI(TAG, "Allocated %"PRIu32" bytes", size);
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

    ESP_ERROR_CHECK(esp_netif_init());

    ESP_ERROR_CHECK(esp_event_loop_create_default());

    /* This helper function configures Wi-Fi or Ethernet, as selected in menuconfig.
     * Read "Establishing Wi-Fi or Ethernet Connection" section in
     * esp-idf/examples/protocols/README.md for more information about this function.
     * Use CONFIG_EXAMPLE_WIFI_SSID and CONFIG_EXAMPLE_WIFI_PASSWORD to change
     * Wi-Fi credentials.
     */
    ESP_ERROR_CHECK(example_connect());

    /* This initializes SNTP for time synchronization.
     * ESP Insights uses relative time since bootup if time is not synchronized and
     * epoch since 1970 if time is synsynchronized.
     */
    esp_rmaker_time_sync_init(NULL);

    esp_insights_config_t config = {
        .log_type = ESP_DIAG_LOG_TYPE_ERROR | ESP_DIAG_LOG_TYPE_WARNING | ESP_DIAG_LOG_TYPE_EVENT,
#ifdef CONFIG_ESP_INSIGHTS_TRANSPORT_HTTPS
        .auth_key = insights_auth_key_start,
#endif
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
