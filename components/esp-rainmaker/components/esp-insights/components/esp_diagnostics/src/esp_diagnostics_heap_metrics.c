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

#include <string.h>
#include <esp_heap_caps.h>
#include <esp_diagnostics.h>
#include <esp_diagnostics_metrics.h>
#include <freertos/FreeRTOS.h>
#include <freertos/timers.h>

#define LOG_TAG            "heap_metrics"
#define METRICS_TAG        "heap"

#define KEY_ALLOC_FAIL     "alloc_fail"
#define KEY_FREE           "free"
#define KEY_MIN_FREE       "min_free_ever"
#define KEY_LFB            "lfb"
#ifdef CONFIG_ESP32_SPIRAM_SUPPORT
#define KEY_EXT_FREE       "ext_free"
#define KEY_EXT_LFB        "ext_lfb"
#define KEY_EXT_MIN_FREE   "ext_min_free_ever"
#endif /* CONFIG_ESP32_SPIRAM_SUPPORT */

#define PATH_HEAP_INTERNAL "heap.internal"
#define PATH_HEAP_EXTERNAL "heap.external"

#define POLLING_INTERVAL        30           /* 30 seconds */
#define TIME_WINDOW             (30 * 60)    /* 1800 seconds = 30 minutes */
#define ITERATIONS_TO_REPORT    (TIME_WINDOW / POLLING_INTERVAL)

#define SEC2TICKS(s)       ((s * 1000) / portTICK_RATE_MS)

typedef struct {
    uint32_t min;
    uint32_t max;
    uint64_t min_ts;
    uint64_t max_ts;
} heap_metrics_data_pt_t;

typedef struct {
    uint32_t period;
    TimerHandle_t handle;
    uint32_t prev_min_free_ever;
    heap_metrics_data_pt_t free;
    heap_metrics_data_pt_t lfb;
#ifdef CONFIG_ESP32_SPIRAM_SUPPORT
    uint32_t prev_ext_min_free_ever;
    heap_metrics_data_pt_t ext_free;
    heap_metrics_data_pt_t ext_lfb;
#endif /* CONFIG_ESP32_SPIRAM_SUPPORT */
} heap_diag_priv_data_t;

static heap_diag_priv_data_t s_priv_data;

#if ESP_IDF_VERSION_MAJOR >= 4 && ESP_IDF_VERSION_MINOR >= 2
static void alloc_failed_hook(size_t size, uint32_t caps, const char *func)
{
    esp_diag_metrics_add_uint(KEY_ALLOC_FAIL, size);
    ESP_DIAG_EVENT(METRICS_TAG, KEY_ALLOC_FAIL " size:0x%x func:%s", size, func);
}
#endif

static void heap_timer_cb(TimerHandle_t handle)
{
    static uint32_t count = ITERATIONS_TO_REPORT;
    uint32_t free;
    uint32_t lfb;
    uint32_t min_free_ever;

#ifdef CONFIG_ESP32_SPIRAM_SUPPORT
    free = heap_caps_get_free_size(MALLOC_CAP_SPIRAM);
    if (free < s_priv_data.ext_free.min) {
        s_priv_data.ext_free.min = free;
        s_priv_data.ext_free.min_ts = esp_diag_timestamp_get();
    }
    if (free > s_priv_data.ext_free.max) {
        s_priv_data.ext_free.max = free;
        s_priv_data.ext_free.max_ts = esp_diag_timestamp_get();
    }

    lfb = heap_caps_get_largest_free_block(MALLOC_CAP_SPIRAM);
    if (lfb < s_priv_data.ext_lfb.min) {
        s_priv_data.ext_lfb.min = lfb;
        s_priv_data.ext_lfb.min_ts = esp_diag_timestamp_get();
    }
    if (lfb > s_priv_data.ext_lfb.max) {
        s_priv_data.ext_lfb.max = lfb;
        s_priv_data.ext_lfb.max_ts = esp_diag_timestamp_get();
    }

    min_free_ever = heap_caps_get_minimum_free_size(MALLOC_CAP_SPIRAM);
    if (min_free_ever < s_priv_data.prev_ext_min_free_ever) {
        esp_diag_metrics_add_uint(KEY_EXT_MIN_FREE, min_free_ever);
        s_priv_data.prev_ext_min_free_ever = min_free_ever;
    }
    if (count == 0) {
        /* Collect min/max for spiram free and lfb */
        esp_diag_metrics_add(ESP_DIAG_DATA_TYPE_UINT, KEY_EXT_FREE, &s_priv_data.ext_free.min, sizeof(uint32_t), s_priv_data.ext_free.min_ts);
        esp_diag_metrics_add(ESP_DIAG_DATA_TYPE_UINT, KEY_EXT_FREE, &s_priv_data.ext_free.max, sizeof(uint32_t), s_priv_data.ext_free.max_ts);
        esp_diag_metrics_add(ESP_DIAG_DATA_TYPE_UINT, KEY_EXT_LFB, &s_priv_data.ext_lfb.min, sizeof(uint32_t), s_priv_data.ext_lfb.min_ts);
        esp_diag_metrics_add(ESP_DIAG_DATA_TYPE_UINT, KEY_EXT_LFB, &s_priv_data.ext_lfb.max, sizeof(uint32_t), s_priv_data.ext_lfb.max_ts);

        /* Reset values */
        s_priv_data.ext_free.min = s_priv_data.ext_free.max = free;
        s_priv_data.ext_free.min_ts = s_priv_data.ext_free.max_ts = esp_diag_timestamp_get();
        s_priv_data.ext_lfb.min = s_priv_data.ext_lfb.max = lfb;
        s_priv_data.ext_lfb.min_ts = s_priv_data.ext_lfb.max_ts = esp_diag_timestamp_get();
    }
#endif /* CONFIG_ESP32_SPIRAM_SUPPORT */

    free = heap_caps_get_free_size(MALLOC_CAP_INTERNAL);
    if (free < s_priv_data.free.min) {
        s_priv_data.free.min = free;
        s_priv_data.free.min_ts = esp_diag_timestamp_get();
    }
    if (free > s_priv_data.free.max) {
        s_priv_data.free.max = free;
        s_priv_data.free.max_ts = esp_diag_timestamp_get();
    }

    lfb = heap_caps_get_largest_free_block(MALLOC_CAP_INTERNAL);
    if (lfb < s_priv_data.lfb.min) {
        s_priv_data.lfb.min = lfb;
        s_priv_data.lfb.min_ts = esp_diag_timestamp_get();
    }
    if (lfb > s_priv_data.lfb.max) {
        s_priv_data.lfb.max = lfb;
        s_priv_data.lfb.max_ts = esp_diag_timestamp_get();
    }

    min_free_ever = heap_caps_get_minimum_free_size(MALLOC_CAP_INTERNAL);
    if (min_free_ever < s_priv_data.prev_min_free_ever) {
        esp_diag_metrics_add_uint(KEY_MIN_FREE, min_free_ever);
        s_priv_data.prev_min_free_ever = min_free_ever;
    }

    if (--count == 0) {
        /* Record min/max for lfb and free heap */
        esp_diag_metrics_add(ESP_DIAG_DATA_TYPE_UINT, KEY_FREE, &s_priv_data.free.min, sizeof(uint32_t), s_priv_data.free.min_ts);
        esp_diag_metrics_add(ESP_DIAG_DATA_TYPE_UINT, KEY_FREE, &s_priv_data.free.max, sizeof(uint32_t), s_priv_data.free.max_ts);
        esp_diag_metrics_add(ESP_DIAG_DATA_TYPE_UINT, KEY_LFB, &s_priv_data.lfb.min, sizeof(uint32_t), s_priv_data.lfb.min_ts);
        esp_diag_metrics_add(ESP_DIAG_DATA_TYPE_UINT, KEY_LFB, &s_priv_data.lfb.max, sizeof(uint32_t), s_priv_data.lfb.max_ts);

        /* Reset min/max */
        s_priv_data.free.min = s_priv_data.free.max = free;
        s_priv_data.free.min_ts = s_priv_data.free.max_ts = esp_diag_timestamp_get();
        s_priv_data.lfb.min = s_priv_data.lfb.max = lfb;
        s_priv_data.lfb.min_ts = s_priv_data.lfb.max_ts = esp_diag_timestamp_get();

        /* Reset counter */
        count = ITERATIONS_TO_REPORT;
    }
}

void esp_diag_heap_metrics_dump(void)
{
    uint32_t free = heap_caps_get_free_size(MALLOC_CAP_INTERNAL);
    uint32_t lfb = heap_caps_get_largest_free_block(MALLOC_CAP_INTERNAL);
    uint32_t min_free_ever = heap_caps_get_minimum_free_size(MALLOC_CAP_INTERNAL);

    esp_diag_metrics_add_uint(KEY_FREE, free);
    esp_diag_metrics_add_uint(KEY_LFB, lfb);
    esp_diag_metrics_add_uint(KEY_MIN_FREE, min_free_ever);

    ESP_LOGI(LOG_TAG, KEY_FREE ":0x%x " KEY_LFB ":0x%x " KEY_MIN_FREE ":0x%x", free, lfb, min_free_ever);
#ifdef CONFIG_ESP32_SPIRAM_SUPPORT
    free = heap_caps_get_free_size(MALLOC_CAP_SPIRAM);
    lfb = heap_caps_get_largest_free_block(MALLOC_CAP_SPIRAM);
    min_free_ever = heap_caps_get_minimum_free_size(MALLOC_CAP_SPIRAM);

    esp_diag_metrics_add_uint(KEY_EXT_FREE, free);
    esp_diag_metrics_add_uint(KEY_EXT_LFB, lfb);
    esp_diag_metrics_add_uint(KEY_EXT_MIN_FREE, min_free_ever);

    ESP_LOGI(LOG_TAG, KEY_EXT_FREE ":0x%x " KEY_EXT_LFB ":0x%x " KEY_EXT_MIN_FREE ":0x%x", free, lfb, min_free_ever);
#endif /* CONFIG_ESP32_SPIRAM_SUPPORT */
}

esp_err_t esp_diag_heap_metrics_init(void)
{
#if ESP_IDF_VERSION_MAJOR >= 4 && ESP_IDF_VERSION_MINOR >= 2
    esp_err_t err = heap_caps_register_failed_alloc_callback(alloc_failed_hook);
    if (err != ESP_OK) {
        return err;
    }
    esp_diag_metrics_register(METRICS_TAG, KEY_ALLOC_FAIL, "Malloc fail", METRICS_TAG, ESP_DIAG_DATA_TYPE_UINT);
#endif

#ifdef CONFIG_ESP32_SPIRAM_SUPPORT
    esp_diag_metrics_register(METRICS_TAG, KEY_EXT_FREE, "External free heap", PATH_HEAP_EXTERNAL, ESP_DIAG_DATA_TYPE_UINT);
    esp_diag_metrics_register(METRICS_TAG, KEY_EXT_LFB, "External largest free block", PATH_HEAP_EXTERNAL, ESP_DIAG_DATA_TYPE_UINT);
    esp_diag_metrics_register(METRICS_TAG, KEY_EXT_MIN_FREE, "External minimum free size", PATH_HEAP_EXTERNAL, ESP_DIAG_DATA_TYPE_UINT);

    s_priv_data.prev_ext_min_free_ever = heap_caps_get_minimum_free_size(MALLOC_CAP_SPIRAM);
    s_priv_data.ext_free.min = s_priv_data.ext_free.max = heap_caps_get_free_size(MALLOC_CAP_SPIRAM);
    s_priv_data.ext_lfb.min = s_priv_data.ext_lfb.max = heap_caps_get_largest_free_block(MALLOC_CAP_SPIRAM);
    s_priv_data.ext_free.min_ts = s_priv_data.ext_free.max_ts = esp_diag_timestamp_get();
    s_priv_data.ext_lfb.min_ts = s_priv_data.ext_lfb.max_ts = esp_diag_timestamp_get();

#endif /* CONFIG_ESP32_SPIRAM_SUPPORT */

    esp_diag_metrics_register(METRICS_TAG, KEY_FREE, "Free heap", PATH_HEAP_INTERNAL, ESP_DIAG_DATA_TYPE_UINT);
    esp_diag_metrics_register(METRICS_TAG, KEY_LFB, "Largest free block", PATH_HEAP_INTERNAL, ESP_DIAG_DATA_TYPE_UINT);
    esp_diag_metrics_register(METRICS_TAG, KEY_MIN_FREE, "Minimum free size", PATH_HEAP_INTERNAL, ESP_DIAG_DATA_TYPE_UINT);

    s_priv_data.prev_min_free_ever = heap_caps_get_minimum_free_size(MALLOC_CAP_INTERNAL);
    s_priv_data.free.min = s_priv_data.free.max = heap_caps_get_free_size(MALLOC_CAP_INTERNAL);
    s_priv_data.lfb.min = s_priv_data.lfb.max = heap_caps_get_largest_free_block(MALLOC_CAP_INTERNAL);
    s_priv_data.free.min_ts = s_priv_data.free.max_ts = esp_diag_timestamp_get();
    s_priv_data.lfb.min_ts = s_priv_data.lfb.max_ts = esp_diag_timestamp_get();

    s_priv_data.period = POLLING_INTERVAL;
    s_priv_data.handle = xTimerCreate("heap_metrics", SEC2TICKS(s_priv_data.period),
                                      pdTRUE, NULL, heap_timer_cb);
    if (s_priv_data.handle) {
        xTimerStart(s_priv_data.handle, 0);
    }
    return ESP_OK;
}

void esp_diag_heap_metrics_reset_period(uint32_t period)
{
    if (period == 0) {
        xTimerStop(s_priv_data.handle, 0);
        return;
    }
    xTimerChangePeriod(s_priv_data.handle, SEC2TICKS(period), 0);
}
