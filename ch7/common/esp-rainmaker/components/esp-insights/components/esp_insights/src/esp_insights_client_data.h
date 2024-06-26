/*
 * SPDX-FileCopyrightText: 2021-2022 Espressif Systems (Shanghai) CO LTD
 *
 * SPDX-License-Identifier: Apache-2.0
 */

#pragma once

#include <stdint.h>
#include <esp_err.h>
#include <esp_rmaker_mqtt_glue.h>

#ifdef __cplusplus
extern "C"
{
#endif
esp_rmaker_mqtt_conn_params_t *esp_insights_get_mqtt_conn_params(void);
void esp_insights_clean_mqtt_conn_params(esp_rmaker_mqtt_conn_params_t *mqtt_conn_params);
esp_err_t esp_insights_meta_nvs_crc_get(uint32_t *crc);
esp_err_t esp_insights_meta_nvs_crc_set(uint32_t crc);
#ifdef __cplusplus
}
#endif
