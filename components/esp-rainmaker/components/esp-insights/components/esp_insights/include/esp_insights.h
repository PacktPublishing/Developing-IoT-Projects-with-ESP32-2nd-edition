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
#include <stdint.h>
#include <stdbool.h>
#include <esp_err.h>
#include <esp_rmaker_mqtt_glue.h>
#include <esp_diagnostics.h>

#ifdef __cplusplus
extern "C"
{
#endif

/**
 * @brief ESP Insights configuration
 */
typedef struct {
    uint32_t log_type;               /*!< Log types to enable, bitwise OR the values from esp_diag_log_type_t */
} esp_insights_config_t;

/**
 * @brief Initialize ESP Insights
 *
 * @param[in] config Configuration for ESP Insights.
 *
 * @return ESP_OK on success.
 * @return error in case of failure.
 */
esp_err_t esp_insights_init(esp_insights_config_t *config);

/**
 * @brief Setup ESP Insights MQTT functions
 *
 * This should be called only if you want to override the default MQTT functions.
 *
 * @param[in] mqtt_config The MQTT configuration.
 *
 * @return ESP_OK on success.
 * @return error in case of failure.
 */
esp_err_t esp_insights_mqtt_setup(esp_rmaker_mqtt_config_t mqtt_config);

#ifdef __cplusplus
}
#endif
