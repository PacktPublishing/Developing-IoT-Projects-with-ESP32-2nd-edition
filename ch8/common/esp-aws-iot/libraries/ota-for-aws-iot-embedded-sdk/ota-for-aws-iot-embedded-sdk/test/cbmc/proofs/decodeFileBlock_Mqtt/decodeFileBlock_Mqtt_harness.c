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
 * @file decodeFileBlock_Mqtt_harness.c
 * @brief Implements the proof harness for decodeFileBlock_Mqtt function.
 */
/* Include headers for mqtt interface. */
#include "ota_mqtt_private.h"

bool OTA_CBOR_Decode_GetStreamResponseMessage( const uint8_t * pMessageBuffer,
                                               size_t messageSize,
                                               int32_t * pFileId,
                                               int32_t * pBlockId,
                                               int32_t * pBlockSize,
                                               uint8_t ** pPayload,
                                               size_t * pPayloadSize )
{
    bool status;

    /* If any of the arguments to the function are not initialized
     * correctly then the functions should return FALSE. */
    if( ( pFileId == NULL ) ||
        ( pBlockId == NULL ) ||
        ( pBlockSize == NULL ) ||
        ( pPayload == NULL ) ||
        ( pPayloadSize == NULL ) ||
        ( pMessageBuffer == NULL ) )
    {
        status = false;
    }

    return status;
}

void decodeFileBlock_Mqtt_harness()
{
    uint8_t * pMessageBuffer;
    size_t messageSize;
    int32_t * pFileId;
    int32_t * pBlockId;
    int32_t * pBlockSize;
    uint8_t ** pPayload;
    size_t * pPayloadSize;

    decodeFileBlock_Mqtt( pMessageBuffer,
                          messageSize,
                          pFileId,
                          pBlockId,
                          pBlockSize,
                          pPayload,
                          pPayloadSize );
}
