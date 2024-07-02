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
 * @file subscribeToJobNotificationTopics_harness.c
 * @brief Implements the proof harness for subscribeToJobNotificationTopics function.
 */
/* Include files required for mqtt interface. */
#include "ota_mqtt_private.h"

/* Maximum size of the pBuffer for subscribeToJobNotificationTopics function. */
#define MAX_TOPIC_NOTIFY_NEXT_BUFFER_SIZE    96U

/* Mangled Name for static function subscribeToJobNotificationTopics. */
OtaMqttStatus_t __CPROVER_file_local_ota_mqtt_c_subscribeToJobNotificationTopics( const OtaAgentContext_t * pAgentCtx );

/* Stub required to combine a set of strings(to form a topic). */
size_t __CPROVER_file_local_ota_mqtt_c_stringBuilder( char * pBuffer,
                                                      size_t bufferSizeBytes,
                                                      const char * strings[] )
{
    size_t stringLength;

    __CPROVER_assert( pBuffer != NULL,
                      "Unable to use pBuffer: passed pointer value is NULL." );

    __CPROVER_assert( strings != NULL,
                      "Unable to use strings: passed pointer value is NULL." );

    /* The size of the static pbuffer is declared inside subscribeToJobNotificationTopics
     * function. */
    __CPROVER_assume( stringLength > 0U && stringLength < MAX_TOPIC_NOTIFY_NEXT_BUFFER_SIZE );

    return stringLength;
}

/* Stub to user defined MQTT-Subscribe operation. */
OtaMqttStatus_t subscribe( const char * pTopicFilter,
                           uint16_t topicFilterLength,
                           uint8_t ucQoS )
{
    OtaMqttStatus_t status;

    return status;
}

/*********************************************************/

void subscribeToJobNotificationTopics_harness()
{
    OtaAgentContext_t agent;
    OtaAgentContext_t * pAgentCtx;

    OtaInterfaces_t otaInterface;

    /* subscribe reference inside the mqtt interface is expected to be initialized by
     * the user and thus assumed to be non-NULL.*/
    otaInterface.mqtt.subscribe = subscribe;
    agent.pOtaInterface = &otaInterface;

    pAgentCtx = &agent;

    ( void ) __CPROVER_file_local_ota_mqtt_c_subscribeToJobNotificationTopics( pAgentCtx );
}
