/* Minimal Diagnostics Example

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
#include "esp_diagnostics_system_metrics.h"
#include "esp_rmaker_utils.h"

#include <freertos/FreeRTOS.h>
#include <freertos/timers.h>

/* Note: Wi-Fi station credentials can be changed using CONFIG_EXAMPLE_WIFI_SSID and CONFIG_EXAMPLE_WIFI_PASSWORD */

#define METRICS_DUMP_INTERVAL_TICKS         ((600 * 1000) / portTICK_PERIOD_MS)

#ifdef CONFIG_ESP_INSIGHTS_TRANSPORT_HTTPS
extern const char insights_auth_key_start[] asm("_binary_insights_auth_key_txt_start");
extern const char insights_auth_key_end[] asm("_binary_insights_auth_key_txt_end");
#endif

static const char *TAG = "minimal_diag";

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
        ESP_LOGE(TAG, "Failed to initialize ESP Insights, err:0x%x", ret);
    }
    ESP_ERROR_CHECK(ret);

    /* Following code generates an example error and logs it */
    nvs_handle_t handle;
    ret = nvs_open("unknown", NVS_READONLY, &handle);
    if (ret != ESP_OK) {
        ESP_LOGE(TAG, "Test error: API nvs_open() failed, error:0x%x", ret);
    }

    /* Please make sure CONFIG_DIAG_ENABLE_METRICS, CONFIG_DIAG_ENABLE_WIFI_METRICS, and CONFIG_DIAG_ENABLE_HEAP_METRICS
     * config options are enabled in order to use esp_diag_heap_metrics_dump() and esp_diag_wifi_metrics_dump() APIs.
     *
     * Enabling the config options CONFIG_DIAG_ENABLE_HEAP_METRICS and CONFIG_DIAG_ENABLE_WIFI_METRICS are enough
     * to start reporting heap and wifi metrics respectively. Following is done to demostrate the use of
     * esp_diag_heap_metrics_dump() and esp_diag_wifi_metrics_dump() APIs and view good graphs on the dashboard.
     */
    while (true) {
        esp_diag_heap_metrics_dump();
        esp_diag_wifi_metrics_dump();
        vTaskDelay(METRICS_DUMP_INTERVAL_TICKS);
    }
}
