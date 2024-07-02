/*
 * SPDX-FileCopyrightText: 2021-2022 Espressif Systems (Shanghai) CO LTD
 *
 * SPDX-License-Identifier: Apache-2.0
 */

#pragma once

#include <esp_err.h>

#ifdef CONFIG_ESP_INSIGHTS_TRANSPORT_MQTT
/* Default configurations for rmaker mqtt glue lib */
extern esp_insights_transport_config_t g_default_insights_transport_mqtt;
#else
/* Default configurations for https */
extern esp_insights_transport_config_t g_default_insights_transport_https;
#endif

/**
 * @brief Perform transport connect
 *
 * @return ESP_OK on success, otherwise appropriate error code
 */
esp_err_t esp_insights_transport_connect(void);

/**
 * @brief Perform transport disconnect
 */
void esp_insights_transport_disconnect(void);

/**
 * @brief Send data using the transport
 *
 * @paran[in] data Data to send
 * @param[in] len  Length of data
 *
 * @return msg_id  Message_id of the sent data.
 *                 On failure, -1
 *                 On success, 0 if data send happens synchronously.
 *                 On success, message-id(positive integer) if data send happened asynchronously.
 */
int esp_insights_transport_data_send(void *data, size_t len);

/**
 * @brief Get node id
 *
 * For MQTT transports if node id is present in factory partition then it is returned,
 * otherwise mac address string is returned.
 *
 * @return node_id
 */
const char *esp_insights_get_node_id(void);
