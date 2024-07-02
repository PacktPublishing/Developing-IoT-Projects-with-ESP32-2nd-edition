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
 * @file unsubscribeFromDataStream_harness.c
 * @brief Implements the proof harness for unsubscribeFromDataStream function.
 */
/* Include headers for mqtt interface. */
#include "ota_mqtt_private.h"

/* Max buffer size for pBuffer for unsubscribeFromDataStream function. */
#define TOPIC_GET_STREAM_BUFFER_SIZE    144

/* Declaration of the test function with the mangled name. */
OtaMqttStatus_t __CPROVER_file_local_ota_mqtt_c_unsubscribeFromDataStream( const OtaAgentContext_t * pAgentCtx );

/* Stub required to combine a set of strings(to form a topic). */
size_t __CPROVER_file_local_ota_mqtt_c_stringBuilder( char * pBuffer,
                                                      size_t bufferSizeBytes,
                                                      const char * strings[] )
{
    size_t stringSize;

    /* pBuffer is initialized in unsubscribeFromDataStream function before passing it to the
     * stringBuilder function and thus cannot be NULL. */
    __CPROVER_assert( pBuffer != NULL,
                      "Unable to use pBuffer: passed pointer value is NULL." );

    /* strings is initialized unsubscribeFromDataStream function before passing it to the
     * stringBuilder function and thus cannot be NULL. */
    __CPROVER_assert( strings != NULL,
                      "Unable to use strings: passed pointer value is NULL." );

    /* The static size of the pBuffer in the unsubscribeFromDataStream function is
     * defined by TOPIC_GET_STREAM_BUFFER_SIZE. Hence, the value stringSize can
     * never exceed TOPIC_GET_STREAM_BUFFER_SIZE. */
    __CPROVER_assume( stringSize > 0 && stringSize < TOPIC_GET_STREAM_BUFFER_SIZE );

    return stringSize;
}

/* Stub to user defined MQTT-unsubscribe operation. */
OtaMqttStatus_t unsubscribe( const char * pTopicFilter,
                             uint16_t topicFilterLength,
                             uint8_t ucQoS )
{
    OtaMqttStatus_t status;

    return status;
}

/*****************************************************************************/

void unsubscribeFromDataStream_harness()
{
    OtaAgentContext_t agent;
    OtaInterfaces_t otaInterface;

    /* unsubscribe reference to the mqtt function is expected to be assigned by the user and thus
     * assumed not to be NULL.*/
    otaInterface.mqtt.unsubscribe = unsubscribe;

    agent.pOtaInterface = &otaInterface;

    /* The agent can never be NULL as it is defined as a global variable in ota.c. */
    ( void ) __CPROVER_file_local_ota_mqtt_c_unsubscribeFromDataStream( &agent );
}
