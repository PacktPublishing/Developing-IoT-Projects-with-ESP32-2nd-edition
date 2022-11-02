// Copyright 2021 Espressif Systems (Shanghai) PTE LTD
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#include <esp_log.h>
#include <esp_wifi.h>
#include <esp_diagnostics_metrics.h>
#include <freertos/FreeRTOS.h>
#include <freertos/timers.h>

#define LOG_TAG            "wifi_metrics"
#define METRICS_TAG        "wifi"
#define KEY_RSSI           "rssi"
#define KEY_MIN_RSSI       "min_rssi_ever"
#define PATH_WIFI_STATION  "Wi-Fi.Station"

#define POLLING_INTERVAL        30   /* 30 seconds */
#define SEC2TICKS(s)            ((s * 1000) / portTICK_RATE_MS)
/* start reporting minimum ever rssi when rssi reaches -50 dbm */
#define WIFI_RSSI_THRESHOLD     -50

typedef struct {
    uint32_t period;
    TimerHandle_t handle;
    int32_t prev_rssi;
    int32_t min_rssi;
} wifi_diag_priv_data_t;

static wifi_diag_priv_data_t s_priv_data;

static void update_min_rssi(int32_t rssi)
{
    if (rssi < s_priv_data.min_rssi) {
        s_priv_data.min_rssi = rssi;
        esp_diag_metrics_add_int(KEY_MIN_RSSI, rssi);
        ets_printf("Wi-Fi RSSI crossed threshold %d\n", rssi);
#if ESP_IDF_VERSION_MAJOR >= 4 && ESP_IDF_VERSION_MINOR >= 3
        esp_wifi_set_rssi_threshold(rssi);
#endif
    }
}

#if ESP_IDF_VERSION_MAJOR >= 4 && ESP_IDF_VERSION_MINOR >= 3

static void wifi_evt_handler(void *arg, esp_event_base_t evt_base, int32_t evt_id, void *evt_data)
{
    if (evt_base == WIFI_EVENT) {
        switch (evt_id) {
            case WIFI_EVENT_STA_BSS_RSSI_LOW:
            {
                wifi_event_bss_rssi_low_t *data = evt_data;
                update_min_rssi(data->rssi);
                break;
            }
            default:
                break;
        }
    }
}
#endif /* ESP_IDF_VERSION_MAJOR >= 4 && ESP_IDF_VERSION_MINOR >= 3 */

/* This function returns 1 on failure otherwise valid RSSI */
static int32_t get_rssi(void)
{
    wifi_ap_record_t ap_info;
    if (esp_wifi_sta_get_ap_info(&ap_info) == ESP_OK) {
        return ap_info.rssi;
    }
    return 1;
}

static void wifi_timer_cb(TimerHandle_t handle)
{
    int32_t rssi = get_rssi();
    if (rssi == 1) {
        return;
    }
    update_min_rssi(rssi);
    if ((rssi / CONFIG_DIAG_WIFI_RSSI_STEP_INTERVAL ) != (s_priv_data.prev_rssi / CONFIG_DIAG_WIFI_RSSI_STEP_INTERVAL)) {
        esp_diag_metrics_add_int(KEY_RSSI, rssi);
        esp_diag_metrics_add_int(KEY_MIN_RSSI, s_priv_data.min_rssi);
    }
    s_priv_data.prev_rssi = rssi;
}

void esp_diag_wifi_metrics_dump(void)
{
    int32_t rssi = get_rssi();
    if (rssi != 1) {
        update_min_rssi(rssi);
        esp_diag_metrics_add_int(KEY_RSSI, rssi);
        s_priv_data.prev_rssi = rssi;
        ESP_LOGI(LOG_TAG, "%s:%d %s:%d", KEY_RSSI, rssi, KEY_MIN_RSSI, s_priv_data.min_rssi);
    }
}

esp_err_t esp_diag_wifi_metrics_init(void)
{
#if ESP_IDF_VERSION_MAJOR >= 4 && ESP_IDF_VERSION_MINOR >= 3
    /* Register the event handler for wifi events */
    esp_err_t err = esp_event_handler_register(WIFI_EVENT, ESP_EVENT_ANY_ID, wifi_evt_handler, NULL);
    if (err != ESP_OK) {
        return err;
    }
    err = esp_wifi_set_rssi_threshold(WIFI_RSSI_THRESHOLD);
    if (err != ESP_OK) {
        ESP_LOGW(LOG_TAG, "Failed to set rssi threshold value");
    }
#endif
    esp_diag_metrics_register(METRICS_TAG, KEY_RSSI, "Wi-Fi RSSI", PATH_WIFI_STATION, ESP_DIAG_DATA_TYPE_INT);
    esp_diag_metrics_register(METRICS_TAG, KEY_MIN_RSSI, "Minimum ever Wi-Fi RSSI", PATH_WIFI_STATION, ESP_DIAG_DATA_TYPE_INT);

    s_priv_data.min_rssi = WIFI_RSSI_THRESHOLD;
    s_priv_data.period = POLLING_INTERVAL;
    s_priv_data.handle = xTimerCreate("wifi_metrics", SEC2TICKS(s_priv_data.period),
                                      pdTRUE, NULL, wifi_timer_cb);
    if (s_priv_data.handle) {
        xTimerStart(s_priv_data.handle, 0);
    }
    /* Record RSSI at start */
    esp_diag_wifi_metrics_dump();
    return ESP_OK;
}
