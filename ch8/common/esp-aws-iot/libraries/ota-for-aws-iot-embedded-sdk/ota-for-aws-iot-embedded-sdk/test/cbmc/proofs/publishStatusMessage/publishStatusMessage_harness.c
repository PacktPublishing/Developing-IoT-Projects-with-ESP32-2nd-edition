/*
 * AWS IoT Over-the-air Update v3.4.0
 * Copyright (C) 2021 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * @file publishStatusMessage_harness.c
 * @brief Implements the proof harness for publishStatusMessage function.
 */
/* Include headers for mqtt interface. */
#include "ota_mqtt_private.h"

#define TOPIC_JOB_STATUS_BUFFER_SIZE    222U            /*!< Max buffer size of pBuffer in publishStatusMessage function. */
#define OTA_STATUS_MSG_MAX_SIZE         128U            /*!< Max length of a job status message to the service. */

/* Declaration of the test function with the mangled name. */
OtaMqttStatus_t __CPROVER_file_local_ota_mqtt_c_publishStatusMessage( OtaAgentContext_t * pAgentCtx,
                                                                      const char * pMsg,
                                                                      uint32_t msgSize,
                                                                      uint8_t qos );

/* Stub required to combine a set of strings(to form a topic). */
size_t __CPROVER_file_local_ota_mqtt_c_stringBuilder( char * pBuffer,
                                                      size_t bufferSizeBytes,
                                                      const char * strings[] )
{
    size_t stringSize;

    /* pBuffer is initialized in publishStatusMessage function before passing it to the
     * stringBuilder function and thus cannot be NULL. */
    __CPROVER_assert( pBuffer != NULL,
                      "Unable to use pBuffer: passed pointer value is NULL." );

    /* strings is initialized publishStatusMessage function before passing it to the
     * stringBuilder function and thus cannot be NULL. */
    __CPROVER_assert( strings != NULL,
                      "Unable to use strings: passed pointer value is NULL." );

    /* The static size of the pBuffer in the publishStatusMessage function is
     * defined by TOPIC_GET_STREAM_BUFFER_SIZE. Hence, the value stringSize can
     * never exceed TOPIC_GET_STREAM_BUFFER_SIZE. */
    __CPROVER_assume( stringSize > 0 && stringSize < TOPIC_JOB_STATUS_BUFFER_SIZE );

    return stringSize;
}

/* Stub to user defined MQTT-publish operation. */
OtaMqttStatus_t publish( const char * const pacTopic,
                         uint16_t usTopicLen,
                         const char * pcMsg,
                         uint32_t ulMsgSize,
                         uint8_t ucQoS )
{
    OtaMqttStatus_t status;

    return status;
}

/*****************************************************************************/

void publishStatusMessage_harness()
{
    OtaAgentContext_t agent;
    OtaInterfaces_t otaInterface;

    /* pMsg is declared statically in the updateJobStatus_Mqtt and passed to publishStatusMessage function. */
    char pMsg[ OTA_STATUS_MSG_MAX_SIZE ];
    uint32_t msgSize;
    uint8_t qos;

    /* publish reference to the mqtt function is expected to be assigned by the user and thus
     * assumed not to be NULL. */
    otaInterface.mqtt.publish = publish;

    agent.pOtaInterface = &otaInterface;

    /* The agent can never be NULL as it is defined as a global variable. */
    ( void ) __CPROVER_file_local_ota_mqtt_c_publishStatusMessage( &agent, pMsg, msgSize, qos );
}
