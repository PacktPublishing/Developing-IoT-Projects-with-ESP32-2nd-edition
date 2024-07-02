/*
 * AWS IoT Over-the-air Update v3.4.0
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * SPDX-License-Identifier: MIT
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

/**
 * @file ota_mqtt_private.h
 * @brief Contains function definitions of routines for OTA download and control using MQTT data plane.
 */

#ifndef OTA_MQTT_H
#define OTA_MQTT_H

/* *INDENT-OFF* */
#ifdef __cplusplus
    extern "C" {
#endif
/* *INDENT-ON* */

/* OTA includes. */
#include "ota.h"
#include "ota_private.h"

/**
 * @brief Check for available OTA job over MQTT.
 *
 * This function Request for the next available OTA job from the job service
 * by publishing a "get next job" message to the job service.
 *
 * @param[in] pAgentCtx The OTA agent context.
 *
 * @return The OTA error code. See OTA Agent error codes information in ota.h.
 */

OtaErr_t requestJob_Mqtt( const OtaAgentContext_t * pAgentCtx );

/**
 * @brief Initialize file transfer over MQTT.
 *
 * This function initializes the file transfer after the OTA job is parsed and accepted
 * by subscribing to the data streaming topics.
 *
 * @param[in] pAgentCtx The OTA agent context.
 *
 * @return The OTA error code. See OTA Agent error codes information in ota.h.
 */

OtaErr_t initFileTransfer_Mqtt( const OtaAgentContext_t * pAgentCtx );

/**
 * @brief Request File block over MQTT.
 *
 * This function is used for requesting a file block over MQTT using the
 * file context.
 *
 * @param[in] pAgentCtx The OTA agent context.
 *
 * @return The OTA PAL layer error code combined with the MCU specific error code. See OTA Agent
 * error codes information in ota.h.
 */

OtaErr_t requestFileBlock_Mqtt( OtaAgentContext_t * pAgentCtx );

/**
 * @brief Decode a cbor encoded fileblock.
 *
 * This function is used for decoding a file block received over MQTT & encoded in cbor.
 *
 * @param[in] pMessageBuffer The message to be decoded.
 * @param[in] messageSize     The size of the message in bytes.
 * @param[out] pFileId        The server file ID.
 * @param[out] pBlockId       The file block ID.
 * @param[out] pBlockSize     The file block size.
 * @param[out] pPayload     The payload.
 * @param[out] pPayloadSize   The payload size.
 *
 * @return The OTA PAL layer error code combined with the MCU specific error code. See OTA Agent
 * error codes information in ota.h.
 */

OtaErr_t decodeFileBlock_Mqtt( const uint8_t * pMessageBuffer,
                               size_t messageSize,
                               int32_t * pFileId,
                               int32_t * pBlockId,
                               int32_t * pBlockSize,
                               uint8_t * const * pPayload,
                               size_t * pPayloadSize );

/**
 * @brief Cleanup related to OTA control plane over MQTT.
 *
 * This function cleanup by unsubscribing from any topics that were
 * subscribed for performing OTA over MQTT.
 *
 * @param[in] pAgentCtx The OTA agent context.
 *
 * @return The OTA error code. See OTA Agent error codes information in ota.h.
 */

OtaErr_t cleanupControl_Mqtt( const OtaAgentContext_t * pAgentCtx );

/**
 * @brief Cleanup related to OTA data plane over MQTT.
 *
 * This function performs cleanup by unsubscribing from any topics that were
 * subscribed for performing OTA data over MQTT.
 *
 * @param[in] pAgentCtx The OTA agent context.
 *
 * @return The OTA error code. See OTA Agent error codes information in ota.h.
 */

OtaErr_t cleanupData_Mqtt( const OtaAgentContext_t * pAgentCtx );

/**
 * @brief Update job status over MQTT.
 *
 * This function updates the OTA job status over MQTT with information like in progress, completion
 * or failure.
 *
 * @param[in] pAgentCtx The OTA agent context.
 *
 * @param[in] status The OTA job status which should be updated. @see OtaJobStatus_t.
 *
 * @param[in] reason The major reason for the status update.
 *
 * @param[in] subReason The platform specific reason.
 *
 * @return The OTA error code. See OTA Agent error codes information in ota.h.
 */

OtaErr_t updateJobStatus_Mqtt( const OtaAgentContext_t * pAgentCtx,
                               OtaJobStatus_t status,
                               int32_t reason,
                               int32_t subReason );

/**
 * @brief Status to string conversion for OTA MQTT interface status.
 *
 * @param[in] status The status to convert to a string.
 *
 * @return The string representation of the status.
 */
const char * OTA_MQTT_strerror( OtaMqttStatus_t status );

/* *INDENT-OFF* */
#ifdef __cplusplus
    }
#endif
/* *INDENT-ON* */

#endif /* ifndef OTA_MQTT_H */
