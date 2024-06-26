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
 * @file requestFileBlock_Mqtt_harness.c
 * @brief Implements the proof harness for requestFileBlock_Mqtt function.
 */
/* Include headers for mqtt interface.*/
#include "ota_mqtt_private.h"

/* Stub required to combine a set of strings(to form a topic). */
size_t __CPROVER_file_local_ota_mqtt_c_stringBuilder( char * pBuffer,
                                                      size_t bufferSizeBytes,
                                                      const char * strings[] )
{
    size_t stringSize;

    /* pBuffer is initialized in requestFileBlock_Mqtt function before passing it to the
     * stringBuilder function and thus cannot be NULL. */
    __CPROVER_assert( pBuffer != NULL,
                      "Unable to use pBuffer: passed pointer value is NULL." );

    /* strings is initialized requestFileBlock_Mqtt function before passing it to the
     * stringBuilder function and thus cannot be NULL. */
    __CPROVER_assert( strings != NULL,
                      "Unable to use strings: passed pointer value is NULL." );

    /* The static size of the pBuffer in the requestFileBlock_Mqtt function is
     * defined by bufferSizeBytes. Hence, the value stringSize can
     * never exceed bufferSizeBytes. */
    __CPROVER_assume( stringSize > 0U && stringSize < bufferSizeBytes );

    return stringSize;
}

/* Stub to encode the stream request message. */
bool OTA_CBOR_Encode_GetStreamRequestMessage( uint8_t * pMessageBuffer,
                                              size_t messageBufferSize,
                                              size_t * pEncodedMessageSize,
                                              const char * pClientToken,
                                              int32_t fileId,
                                              int32_t blockSize,
                                              int32_t blockOffset,
                                              uint8_t * pBlockBitmap,
                                              size_t blockBitmapSize,
                                              int32_t numOfBlocksRequested )
{
    bool cborEncodeRet;

    return cborEncodeRet;
}

/* Stub to user defined MQTT-publish operation. */
OtaMqttStatus_t stubMqttPublish( const char * const pacTopic,
                                 uint16_t usTopicLen,
                                 const char * pcMsg,
                                 uint32_t ulMsgSize,
                                 uint8_t ucQoS )
{
    OtaMqttStatus_t mqttstatus;

    return mqttstatus;
}

/*****************************************************************************/
void requestFileBlock_Mqtt_harness()
{
    OtaAgentContext_t * pAgentCtx;
    OtaMqttInterface_t mqtt;
    OtaAgentContext_t agent;
    OtaInterfaces_t otaInterface;

    /* publish reference to the mqtt function is expected to be assigned by the user and thus
     * assumed not to be NULL. */
    otaInterface.mqtt.publish = stubMqttPublish;

    /* requestFileBlock_Mqtt is called only when there is a firmware image available.
     * The size of the image is always less than 4GB. */
    __CPROVER_assume( agent.fileContext.fileSize > 0 && agent.fileContext.fileSize < INT32_MAX - OTA_FILE_BLOCK_SIZE );

    /* serverFileID is typecasted to int32_t and thus it's values cannot
     * exceed INT32_MAX. */
    __CPROVER_assume( agent.fileContext.serverFileID < INT32_MAX );

    agent.pOtaInterface = &otaInterface;

    /* OTA agent is defined as a global variable in ota.c and thus cannot be NULL.*/
    pAgentCtx = &agent;

    requestFileBlock_Mqtt( pAgentCtx );
}
