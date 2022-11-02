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
#pragma once

#ifdef __cplusplus
extern "C"
{
#endif

#if CONFIG_DIAG_ENABLE_HEAP_METRICS

/**
 * @brief Initialize the heap metrics
 *
 * This API starts polling free memory, largest free block every 30 seconds and collects minimum and maximum values
 * in 30 minutes time interval. It also starts polling minimum free memory and if that value drops
 * to a new low (low watermark) only then it is collected.
 *
 * Parameters are collected for RAM in internal memory and external memory (if device has PSRAM).
 *
 * @return ESP_OK if successful, appropriate error code otherwise.
 */
esp_err_t esp_diag_heap_metrics_init(void);

/**
 * @brief Reset the periodic interval
 *
 * @param[in] period Period interval in seconds
 */
void esp_diag_heap_metrics_reset_period(uint32_t period);

/**
 * @brief Dumps the heap metrics and prints them to the console.
 *
 * This API collects and reports metrics value at any give point in time.
 */
void esp_diag_heap_metrics_dump(void);

#endif /* CONFIG_DIAG_ENABLE_HEAP_METRICS */

#if CONFIG_DIAG_ENABLE_WIFI_METRICS

/**
 * @brief Initialize the wifi metrics
 *
 * Wi-Fi metrics collects the wifi RSSI and minimum ever RSSI.
 *
 * @return ESP_OK if successful, appropriate error code otherwise.
 */
esp_err_t esp_diag_wifi_metrics_init(void);

/**
 * @brief Dumps the wifi metrics and prints them to the console.
 *
 * This API can be used to collect wifi metrics at any given point in time.
 */
void esp_diag_wifi_metrics_dump(void);

#endif /* CONFIG_DIAG_ENABLE_WIFI_METRICS */

#ifdef __cplusplus
}
#endif
