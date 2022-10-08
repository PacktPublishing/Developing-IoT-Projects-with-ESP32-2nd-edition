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
#include <esp_log.h>
#include <esp_wifi.h>
#include <freertos/FreeRTOS.h>
#include <freertos/timers.h>
#include <freertos/semphr.h>
#include <rtc_store.h>
#include <esp_diagnostics.h>
#include <esp_diagnostics_metrics.h>
#include <esp_diagnostics_variables.h>
#include <esp_diagnostics_system_metrics.h>
#include <esp_diagnostics_network_variables.h>
#include <esp_rmaker_common_events.h>
#include <esp_rmaker_factory.h>
#include <esp_rmaker_work_queue.h>
#include <esp_insights.h>

#include "esp_insights_mqtt.h"
#include "esp_insights_client_data.h"
#include "esp_insights_encoder.h"

#define INSIGHTS_TOPIC_SUFFIX       "diagnostics/from-node"
#define INSIGHTS_DEBUG_ENABLED      CONFIG_ESP_INSIGHTS_DEBUG_ENABLED
#define APP_ELF_SHA256_LEN          (CONFIG_APP_RETRIEVE_LEN_ELF_SHA + 1)

#define CLOUD_REPORTING_PERIOD_MIN_SEC    (1 * 60)  /* 1 minute */
#define CLOUD_REPORTING_PERIOD_MAX_SEC    (60 * 60)  /* 60 minutes */

#if CONFIG_RTC_STORE_DATA_SIZE > (1024 * 4)
#define INSIGHTS_DATA_MAX_SIZE  (CONFIG_RTC_STORE_DATA_SIZE - 1024)
#else
#define INSIGHTS_DATA_MAX_SIZE  CONFIG_RTC_STORE_DATA_SIZE
#endif

#define SEND_INSIGHTS_META (CONFIG_DIAG_ENABLE_METRICS || CONFIG_DIAG_ENABLE_VARIABLES)
#define KEY_LOG_WR_FAIL    "log_wr_fail"

typedef struct esp_insights_entry {
    esp_rmaker_work_fn_t work_fn;
    TimerHandle_t timer;
    uint32_t min_seconds;
    uint32_t max_seconds;
    uint32_t cur_seconds;
    void *priv_data;
} esp_insights_entry_t;

typedef struct {
    uint8_t *scratch_buf;
    int mqtt_pub_msg_id;
    uint32_t mqtt_pub_msg_len;
    SemaphoreHandle_t mqtt_lock;
    char app_sha256[APP_ELF_SHA256_LEN];
    esp_rmaker_mqtt_conn_params_t *mqtt_conn_params;
    char *node_id;
    bool data_sent;
#if SEND_INSIGHTS_META
    bool meta_msg_pending;
    uint32_t meta_msg_id;
#endif /* SEND_INSIGHTS_META */
    bool data_send_inprogress;
    uint32_t log_write_fail_cnt; /* Count of failed log write */
} esp_insights_data_t;

#ifdef CONFIG_ESP_INSIGHTS_ENABLED

static const char *TAG = "esp_insights";
static esp_insights_data_t s_insights_data;

static void esp_insights_first_call(void *priv_data)
{
    if (!priv_data) {
        return;
    }
    esp_insights_entry_t *entry = (esp_insights_entry_t *)priv_data;
    esp_rmaker_work_queue_add_task(entry->work_fn, entry->priv_data);
    /* Start timer here so that the function is called periodically */
    ESP_LOGI(TAG, "Scheduling Insights timer for %d seconds.", entry->cur_seconds);
    xTimerStart(entry->timer, 0);
}

/* This should be used only from the handler registered using esp_insights_register_periodic_handler(). */
static esp_err_t esp_insights_send_data(void *data, size_t len, int *msg_id)
{
    char publish_topic[100];

    if (!data) {
        return ESP_ERR_INVALID_ARG;
    }
    if (!s_insights_data.node_id) {
        return ESP_FAIL;
    }
    snprintf(publish_topic, sizeof(publish_topic), "node/%s/%s", s_insights_data.node_id, INSIGHTS_TOPIC_SUFFIX);
    esp_err_t err = esp_insights_mqtt_publish(publish_topic, data, len, RMAKER_MQTT_QOS1, msg_id);
    if (err != ESP_OK) {
        ESP_LOGE(TAG, "esp_insights_mqtt_publish_data returned error %d", err);
    }
    return err;
}

/* This executes in the context of timer task.
 *
 * There is a dynamic logic to decide the next instance when the insights
 * data will be reported. Depending on whether data was sent or not during
 * the previous timeout, we double or halve the time period.
 * This ensures that data generally gets reported quick enough,
 * but if there's very frequent data being generated, it wont result
 * into too frquent publishes.
 * The period will keep changing between CLOUD_REPORTING_PERIOD_MIN_SEC and
 * CLOUD_REPORTING_PERIOD_MAX_SEC
 */
static void esp_insights_common_cb(TimerHandle_t handle)
{
    esp_insights_entry_t *entry = (esp_insights_entry_t *)pvTimerGetTimerID(handle);
    /* Check if any data was sent during the previous time out */
    xSemaphoreTake(s_insights_data.mqtt_lock, portMAX_DELAY);
    bool l_data_sent = s_insights_data.data_sent;
    s_insights_data.data_sent = false;
    xSemaphoreGive(s_insights_data.mqtt_lock);

    if (entry) {
        esp_rmaker_work_queue_add_task(entry->work_fn, entry->priv_data);
        /* If data was sent during previous timer interval, double the period */
        if (l_data_sent) {
            entry->cur_seconds <<= 1; /* Double the period */
            if (entry->cur_seconds > entry->max_seconds) {
                entry->cur_seconds = entry->max_seconds;
            }
        } else {
            /* If no data was sent during previous timer interval, halve the period */
            entry->cur_seconds >>= 1; /* Halve the period */
            if (entry->cur_seconds < entry->min_seconds) {
                entry->cur_seconds = entry->min_seconds;
            }
        }
        xTimerChangePeriod(handle, (entry->cur_seconds * 1000)/ portTICK_PERIOD_MS, 100);
        ESP_LOGI(TAG, "Scheduling Insights timer for %d seconds.", entry->cur_seconds);
        xTimerStart(handle, 0);
    }
}

static esp_err_t esp_insights_register_periodic_handler(esp_rmaker_work_fn_t work_fn,
                                                        uint32_t min_seconds, uint32_t max_seconds,
                                                        void *priv_data)
{
    if (!work_fn || (min_seconds == 0) || (max_seconds == 0)) {
        return ESP_FAIL;
    }

    esp_insights_entry_t *insights_entry = calloc (1, sizeof(esp_insights_entry_t));
    if (!insights_entry) {
        return ESP_FAIL;
    }
    insights_entry->work_fn = work_fn;
    insights_entry->priv_data = priv_data;
    insights_entry->min_seconds = min_seconds;
    insights_entry->max_seconds = max_seconds;
    insights_entry->cur_seconds = min_seconds;
    insights_entry->timer = xTimerCreate("test", (insights_entry->cur_seconds * 1000)/ portTICK_PERIOD_MS, pdFALSE, (void *)insights_entry, esp_insights_common_cb);
    if (!insights_entry->timer) {
        free(insights_entry);
        return ESP_FAIL;
    }
    /* Rainmaker work queue execution start after MQTT connection is established,
     * esp_insights_first_call() will be executed after MQTT connection is established.
     * It add the work_fn to the queue and start the periodic timer.
     */
    return esp_rmaker_work_queue_add_task(esp_insights_first_call, insights_entry);
}

/* This executes in the context of default event loop task */
static void insights_event_handler(void* arg, esp_event_base_t event_base,
                                   int32_t event_id, void* event_data)
{
    int msg_id;
    if (event_base != RMAKER_COMMON_EVENT) {
        return;
    }
    switch(event_id) {
        case RMAKER_MQTT_EVENT_CONNECTED:
        /* Checking and populating node id again here, because for some use cases,
         * the node id may not be available while enabling esp insights, but something
         * that could be initialised later.
         */
            if (!s_insights_data.node_id) {
                s_insights_data.node_id = esp_insights_get_node_id();
                if (s_insights_data.node_id) {
                    ESP_LOGI(TAG, "ESP Insights enabled for Node ID ----- %s", s_insights_data.node_id);
                }
            }
            break;
        case RMAKER_MQTT_EVENT_PUBLISHED:
            msg_id = *((int *)event_data);
#if INSIGHTS_DEBUG_ENABLED
            ESP_LOGI(TAG, "MQTT Published. Msg id: %d.", msg_id);
#endif
            if (msg_id) {
                xSemaphoreTake(s_insights_data.mqtt_lock, portMAX_DELAY);
                if (msg_id == s_insights_data.mqtt_pub_msg_id) {
                    rtc_store_critical_data_release(s_insights_data.mqtt_pub_msg_len);
                    s_insights_data.data_sent = true;
                    s_insights_data.data_send_inprogress = false;
#if SEND_INSIGHTS_META
                } else if (s_insights_data.meta_msg_pending && msg_id == s_insights_data.meta_msg_id) {
                    esp_insights_meta_nvs_crc_set(esp_diag_meta_crc_get());
                    s_insights_data.meta_msg_pending = false;
                    s_insights_data.data_sent = true;
#endif /* SEND_INSIGHTS_META */
                }
                xSemaphoreGive(s_insights_data.mqtt_lock);
            }
            break;
        default:
            break;
    }
}

#if INSIGHTS_DEBUG_ENABLED
static void hex_dump(uint8_t *data, uint32_t len)
{
    int index;
    for (index = 0; index < len; index++) {
        if ((index % 16) == 0) {
            printf("\n");
        }
        printf("0x%02x ", s_insights_data.scratch_buf[index]);
    }
    printf("\n");
}
#endif /* INSIGHTS_DEBUG_ENABLED */

#if SEND_INSIGHTS_META
/* Returns true if ESP Insights metadata CRC is changed */
static bool insights_meta_changed(void)
{
    uint32_t nvs_crc;
    uint32_t meta_crc = esp_diag_meta_crc_get();
    esp_err_t err = esp_insights_meta_nvs_crc_get(&nvs_crc);
    if (err == ESP_OK && nvs_crc == meta_crc) {
        /* crc found and matched, no need to send insights meta */
        return false;
    }
    ESP_LOGI(TAG, "Insights metrics metadata changed");
    return true;
}

static void send_insights_meta(void)
{
    int msg_id;
    uint16_t len = 0;
    esp_err_t err;

    memset(s_insights_data.scratch_buf, 0, INSIGHTS_DATA_MAX_SIZE);
    len = esp_insights_encode_meta(s_insights_data.scratch_buf, INSIGHTS_DATA_MAX_SIZE, s_insights_data.app_sha256);
    if (len == 0) {
#if INSIGHTS_DEBUG_ENABLED
        ESP_LOGI(TAG, "No metadata to send");
#endif
        return;
    }
#if INSIGHTS_DEBUG_ENABLED
    ESP_LOGI(TAG, "Insights meta data length %d", len);
    hex_dump(s_insights_data.scratch_buf, len);
#endif
    err = esp_insights_send_data(s_insights_data.scratch_buf, len, &msg_id);
    if (err == ESP_OK) {
        if (msg_id > 0) {
            xSemaphoreTake(s_insights_data.mqtt_lock, portMAX_DELAY);
            s_insights_data.meta_msg_pending = true;
            s_insights_data.meta_msg_id = msg_id;
            xSemaphoreGive(s_insights_data.mqtt_lock);
        } else if (msg_id == 0) {
            esp_insights_meta_nvs_crc_set(esp_diag_meta_crc_get());
        }
    } else {
        ESP_LOGW(TAG, "Insights meta send failed");
    }
}
#endif /* SEND_INSIGHTS_META */

static size_t encode_data(const void *critical_data, size_t critical_data_size,
                          const void *non_critical_data, size_t non_critical_data_size,
                          void *out_data, size_t out_data_size)
{
    static bool first_time = true;

    if (!out_data || !out_data_size) {
        return 0;
    }
    if (!first_time && !critical_data && !non_critical_data) {
        return 0;
    }
    esp_insights_encode_data_begin(out_data, out_data_size, s_insights_data.app_sha256);
    if (first_time) {
        esp_insights_encode_boottime_data();
        first_time = false;
    }
    if (critical_data) {
        esp_insights_encode_critical_data(critical_data, critical_data_size);
    }
    if (non_critical_data) {
        esp_insights_encode_non_critical_data(non_critical_data, non_critical_data_size);
    }
    return esp_insights_encode_data_end(out_data);
}

/* Consider 100 bytes are published and received on cloud but RMAKER_MQTT_EVENT_PUBLISHED
 * event is not received for 100 bytes. In a mean time 50 bytes are added to the buffer.
 * When the next time timer expires then old 100 bytes plus new 50 bytes will be published
 * and if RMAKER_MQTT_EVENT_PUBLISHED event is recieve for the new message then 150 bytes
 * will be removed from the buffers.
 *
 * In short, there is the possibility of data duplication, so cloud should be able to handle it.
 */

/* This encodes and sends insights data */
static void send_insights_data(void)
{
    uint16_t len = 0;
    esp_err_t err;
    const void *critical_data = NULL;
    const void *non_critical_data = NULL;
    size_t critical_data_size = 0;
    size_t non_critical_data_size = 0;
    int msg_id = -1;

    memset(s_insights_data.scratch_buf, 0, INSIGHTS_DATA_MAX_SIZE);

#if CONFIG_DIAG_ENABLE_VARIABLES
    static uint32_t prev_log_write_fail_cnt = 0;
    if (s_insights_data.log_write_fail_cnt > prev_log_write_fail_cnt) {
        prev_log_write_fail_cnt = s_insights_data.log_write_fail_cnt;
        esp_diag_variable_add_uint(KEY_LOG_WR_FAIL, prev_log_write_fail_cnt);
    }
#endif /* CONFIG_DIAG_ENABLE_VARIABLES */

    critical_data = rtc_store_critical_data_read_and_lock(&critical_data_size);
    non_critical_data = rtc_store_non_critical_data_read_and_lock(&non_critical_data_size);
    len = encode_data(critical_data, critical_data_size,
                      non_critical_data, non_critical_data_size,
                      s_insights_data.scratch_buf, INSIGHTS_DATA_MAX_SIZE);
    if (critical_data) {
        /* If any ESP_LOGE, ESP_LOGW is added in between rtc_store_critical_data_read_and_lock()
         * and rtc_store_critical_data_release_and_unlock(), system will be deadlocked.
         * Unlocking here as soon as possible.
         */
        rtc_store_critical_data_release_and_unlock(0);
    }
    if (non_critical_data) {
        /* Remove the non critical data after encoding */
        rtc_store_non_critical_data_release_and_unlock(non_critical_data_size);
    }
    if (len == 0) {
#if INSIGHTS_DEBUG_ENABLED
        ESP_LOGI(TAG, "No data to send");
#endif
        return;
    }
#if INSIGHTS_DEBUG_ENABLED
    ESP_LOGI(TAG, "Sending data of length %d to the MQTT Insights topic:", len);
    hex_dump(s_insights_data.scratch_buf, len);
#endif
    err = esp_insights_send_data(s_insights_data.scratch_buf, len, &msg_id);
    if (err == ESP_OK) {
        if (msg_id > 0) {
            /* Published with QOS1, store the msg_id and wait for PUBLISHED event */
            xSemaphoreTake(s_insights_data.mqtt_lock, portMAX_DELAY);
            s_insights_data.mqtt_pub_msg_len = critical_data_size;
            s_insights_data.mqtt_pub_msg_id = msg_id;
            xSemaphoreGive(s_insights_data.mqtt_lock);
        } else if (msg_id == 0) {
            /* Published with QOS0, remove the read data from the ringbuffer */
            rtc_store_critical_data_release(critical_data_size);
            xSemaphoreTake(s_insights_data.mqtt_lock, portMAX_DELAY);
            s_insights_data.data_sent = true;
            s_insights_data.data_send_inprogress = false;
            xSemaphoreGive(s_insights_data.mqtt_lock);
        }
    }
}

static void insights_periodic_handler(void *priv_data)
{
    xSemaphoreTake(s_insights_data.mqtt_lock, portMAX_DELAY);
    /* Return if wifi is disconnected */
    wifi_ap_record_t ap_info;
    if (esp_wifi_sta_get_ap_info(&ap_info) != ESP_OK) {
        s_insights_data.data_send_inprogress = false;
        xSemaphoreGive(s_insights_data.mqtt_lock);
        return;
    }
    if (s_insights_data.data_send_inprogress) {
        xSemaphoreGive(s_insights_data.mqtt_lock);
        return;
    }
    s_insights_data.data_send_inprogress = true;
    xSemaphoreGive(s_insights_data.mqtt_lock);
#if SEND_INSIGHTS_META
    if (insights_meta_changed()) {
        send_insights_meta();
    }
#endif /* SEND_INSIGHTS_META */
    send_insights_data();
}

static void rtc_store_event_handler(void* arg, esp_event_base_t event_base,
                                    int32_t event_id, void* event_data)
{
    if (event_base != RTC_STORE_EVENT) {
        return;
    }
    switch(event_id) {
        case RTC_STORE_EVENT_CRITICAL_DATA_LOW_MEM:
        {
#if INSIGHTS_DEBUG_ENABLED
            ESP_LOGI(TAG, "RTC_STORE_EVENT_CRITICAL_DATA_LOW_MEM");
#endif
            esp_rmaker_work_queue_add_task(insights_periodic_handler, NULL);
            break;
        }
        case RTC_STORE_EVENT_CRITICAL_DATA_WRITE_FAIL:
            s_insights_data.log_write_fail_cnt++;
#if INSIGHTS_DEBUG_ENABLED
            ESP_LOGI(TAG, "Log write fail count: %d", s_insights_data.log_write_fail_cnt);
#endif
            break;
        default:
            break;
    }
}

static esp_err_t log_write_cb(void *data, size_t len, void *priv_data)
{
    return rtc_store_critical_data_write(data, len);
}

#if CONFIG_DIAG_ENABLE_METRICS
static esp_err_t metrics_write_cb(const char *group, void *data, size_t len, void *cb_arg)
{
    return rtc_store_non_critical_data_write(group, data, len);
}
#endif /* CONFIG_DIAG_ENABLE_METRICS */

#if CONFIG_DIAG_ENABLE_VARIABLES
static esp_err_t variables_write_cb(const char *group, void *data, size_t len, void *cb_arg)
{
    return rtc_store_non_critical_data_write(group, data, len);
}
#endif /* CONFIG_DIAG_ENABLE_VARIABLES */

static void esp_insights_deinit(void)
{
    if (s_insights_data.node_id) {
        free(s_insights_data.node_id);
        s_insights_data.node_id = NULL;
    }
    if (s_insights_data.scratch_buf) {
        free(s_insights_data.scratch_buf);
        s_insights_data.scratch_buf = NULL;
    }
    if (s_insights_data.mqtt_lock) {
        vSemaphoreDelete(s_insights_data.mqtt_lock);
        s_insights_data.mqtt_lock = NULL;
    }
    if (s_insights_data.mqtt_conn_params) {
        esp_insights_clean_mqtt_conn_params(s_insights_data.mqtt_conn_params);
        free(s_insights_data.mqtt_conn_params);
        s_insights_data.mqtt_conn_params = NULL;
    }
}

esp_err_t esp_insights_enable(esp_insights_config_t *config)
{
    if (!config) {
        return ESP_ERR_INVALID_ARG;
    }
    if (s_insights_data.mqtt_lock) {
        ESP_LOGW(TAG, "Insights already enabled");
        return ESP_OK;
    }
    s_insights_data.mqtt_lock = xSemaphoreCreateMutex();
    if (!s_insights_data.mqtt_lock) {
        ESP_LOGE(TAG, "Failed to create mqtt lock.");
        return ESP_ERR_NO_MEM;
    }
    s_insights_data.scratch_buf = malloc(INSIGHTS_DATA_MAX_SIZE);
    if (!s_insights_data.scratch_buf) {
        ESP_LOGE(TAG, "Failed to allocate memory for scratch buffer.");
        vSemaphoreDelete(s_insights_data.mqtt_lock);
        s_insights_data.mqtt_lock = NULL;
        return ESP_ERR_NO_MEM;
    }
    /* Get sha256 */
    esp_diag_device_info_t device_info;
    memset(&device_info, 0, sizeof(device_info));
    esp_err_t err = esp_diag_device_info_get(&device_info);
    if (err != ESP_OK) {
        ESP_LOGE(TAG, "Failed to get device info");
        goto enable_err;
    }
    memcpy(s_insights_data.app_sha256, device_info.app_elf_sha256, sizeof(s_insights_data.app_sha256));
    err = esp_event_handler_register(RMAKER_COMMON_EVENT, ESP_EVENT_ANY_ID, insights_event_handler, NULL);
    if (err != ESP_OK) {
        ESP_LOGE(TAG, "Failed to register event handler for RMAKER_COMMON_EVENT");
        goto enable_err;
    }
    /* Register event handler for rtc store events */
    err = esp_event_handler_register(RTC_STORE_EVENT, ESP_EVENT_ANY_ID, rtc_store_event_handler, NULL);
    if (err != ESP_OK) {
        ESP_LOGE(TAG, "Failed to register event handler for RTC_STORE_EVENT");
        goto enable_err;
    }
    err = rtc_store_init();
    if (err != ESP_OK) {
        ESP_LOGE(TAG, "Failed to initialise RTC store.");
        goto enable_err;
    }
    esp_diag_log_config_t log_config = {
        .write_cb = log_write_cb,
        .cb_arg = NULL,
    };
    err = esp_diag_log_hook_init(&log_config);
    if (err != ESP_OK) {
        ESP_LOGE(TAG, "Failed to initialise Log hook.");
        goto enable_err;
    }
    esp_diag_log_hook_enable(config->log_type);

#if CONFIG_DIAG_ENABLE_METRICS
    /* Initialize and enable metrics */
    esp_diag_metrics_config_t metrics_config = {
        .write_cb = metrics_write_cb,
        .cb_arg = NULL,
    };
    err = esp_diag_metrics_init(&metrics_config);
    if (err != ESP_OK) {
        ESP_LOGE(TAG, "Failed to initialize metrics.");
    }
#if CONFIG_DIAG_ENABLE_HEAP_METRICS
    err = esp_diag_heap_metrics_init();
    if (err != ESP_OK) {
        ESP_LOGW(TAG, "Failed to initialize heap metrics");
    }
#endif /* CONFIG_DIAG_ENABLE_HEAP_METRICS */
#if CONFIG_DIAG_ENABLE_WIFI_METRICS
    err = esp_diag_wifi_metrics_init();
    if (err != ESP_OK) {
        ESP_LOGW(TAG, "Failed to initialize wifi metrics");
    }
#endif /* CONFIG_DIAG_ENABLE_WIFI_METRICS */
#endif /* CONFIG_DIAG_ENABLE_METRICS */

#if CONFIG_DIAG_ENABLE_VARIABLES
    /* Initialize and enable param-values */
    esp_diag_variable_config_t variable_config = {
        .write_cb = variables_write_cb,
        .cb_arg = NULL,
    };
    err = esp_diag_variable_init(&variable_config);
    if (err != ESP_OK) {
        ESP_LOGE(TAG, "Failed to initialize param-values.");
    }
#if CONFIG_DIAG_ENABLE_NETWORK_VARIABLES
    err = esp_diag_network_variables_init();
    if (err != ESP_OK) {
        ESP_LOGW(TAG, "Failed to initialize network variables");
    }
#endif /* CONFIG_DIAG_ENABLE_NETWORK_VARIABLES */
    esp_diag_variable_register("diag", KEY_LOG_WR_FAIL, "Log write fail count", "Diagnostics.Log", ESP_DIAG_DATA_TYPE_UINT);
#endif /* CONFIG_DIAG_ENABLE_VARIABLES */

    err = esp_insights_register_periodic_handler(insights_periodic_handler,
                CLOUD_REPORTING_PERIOD_MIN_SEC, CLOUD_REPORTING_PERIOD_MAX_SEC, NULL);
    if (err != ESP_OK) {
        ESP_LOGE(TAG, "Failed to register insights_periodic_handler.");
        goto enable_err;
    }
    if (!s_insights_data.node_id) {
        s_insights_data.node_id = esp_insights_get_node_id();
        if (s_insights_data.node_id) {
            ESP_LOGI(TAG, "ESP Insights enabled for Node ID ----- %s", s_insights_data.node_id);
        }
    }
    return ESP_OK;
enable_err:
    vSemaphoreDelete(s_insights_data.mqtt_lock);
    s_insights_data.mqtt_lock = NULL;
    free(s_insights_data.scratch_buf);
    s_insights_data.scratch_buf = NULL;
    return err;
}

esp_err_t esp_insights_init(esp_insights_config_t *config)
{
    esp_err_t err;
    if (!config) {
        return ESP_ERR_INVALID_ARG;
    }
    if (s_insights_data.mqtt_lock) {
        ESP_LOGW(TAG, "ESP Insights already initialized");
        return ESP_OK;
    }
    if (esp_rmaker_factory_init() != ESP_OK) {
        ESP_LOGE(TAG, "Failed to initialise factory storage.");
        return ESP_FAIL;
    }
    s_insights_data.mqtt_conn_params = esp_insights_get_mqtt_conn_params();
    if (!s_insights_data.mqtt_conn_params) {
        ESP_LOGE(TAG, "Failed to get MQTT connection parameters.");
        return ESP_FAIL;
    }
    err = esp_insights_mqtt_init(s_insights_data.mqtt_conn_params);
    if (err != ESP_OK) {
        ESP_LOGE(TAG, "Failed to initialise MQTT, err:%d.", err);
        goto init_err;
    }
    err = esp_rmaker_work_queue_init();
    if (err != ESP_OK) {
        ESP_LOGE(TAG, "Failed to initialise Work Queue.");
        goto init_err;
    }
    err = esp_insights_enable(config);
    if (err != ESP_OK) {
        ESP_LOGE(TAG, "Failed to Enable ESP Insights.");
        goto init_err;
    }
    err = esp_insights_mqtt_connect();
    if (err != ESP_OK) {
        ESP_LOGE(TAG, "Failed to connect to MQTT.");
        goto init_err;
    }
    err = esp_rmaker_work_queue_start();
    if (err != ESP_OK) {
        ESP_LOGE(TAG, "Failed to start Work Queue.");
        goto init_err;
    }
    return ESP_OK;
init_err:
    esp_insights_deinit();
    return err;
}

#endif /* CONFIG_ESP_INSIGHTS_ENABLED */
