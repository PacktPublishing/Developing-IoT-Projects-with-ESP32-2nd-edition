/*
 * SPDX-FileCopyrightText: 2021-2022 Espressif Systems (Shanghai) CO LTD
 *
 * SPDX-License-Identifier: Apache-2.0
 */

#pragma once

#include <cbor.h>
#include <esp_diagnostics_metrics.h>
#include <esp_diagnostics_variables.h>
#if CONFIG_ESP_INSIGHTS_COREDUMP_ENABLE
#include <esp_core_dump.h>
#endif /* CONFIG_ESP_INSIGHTS_COREDUMP_ENABLE */
#include <rtc_store.h>

void esp_insights_cbor_encode_diag_begin(void *data, size_t data_size, const char *version);
void esp_insights_cbor_encode_diag_data_begin(void);
void esp_insights_cbor_encode_diag_boot_info(esp_diag_device_info_t *device_info);

/**
 * @brief encode master header
 *
 * @param hdr meta header which contains data regarding message it follows
 * @param type rtc_store type (viz., "critical", "non_critical")
 */
void esp_insights_cbor_encode_meta_c_hdr(const rtc_store_meta_header_t *hdr);
void esp_insights_cbor_encode_meta_nc_hdr(const rtc_store_meta_header_t *hdr);

#if CONFIG_ESP_INSIGHTS_COREDUMP_ENABLE
void esp_insights_cbor_encode_diag_crash(esp_core_dump_summary_t *summary);
#endif /* CONFIG_ESP_INSIGHTS_COREDUMP_ENABLE */
size_t esp_insights_cbor_encode_diag_logs(const uint8_t *data, size_t size);
size_t esp_insights_cbor_encode_diag_metrics(const uint8_t *data, size_t size);
size_t esp_insights_cbor_encode_diag_variables(const uint8_t *data, size_t size);
void esp_insights_cbor_encode_diag_data_end(void);
size_t esp_insights_cbor_encode_diag_end(void *data);

/* For encoding diag meta data */
void esp_insights_cbor_encode_meta_begin(void *data, size_t data_size, const char *version, const char *sha256);
void esp_insights_cbor_encode_meta_data_begin(void);
#if CONFIG_DIAG_ENABLE_METRICS
void esp_insights_cbor_encode_meta_metrics(const esp_diag_metrics_meta_t *metrics, uint32_t metrics_len);
#endif /* CONFIG_DIAG_ENABLE_METRICS */
#if CONFIG_DIAG_ENABLE_VARIABLES
void esp_insights_cbor_encode_meta_variables(const esp_diag_variable_meta_t *variables, uint32_t variables_len);
#endif /* CONFIG_DIAG_ENABLE_VARIABLES */
void esp_insights_cbor_encode_meta_data_end(void);
size_t esp_insights_cbor_encode_meta_end(void *data);
