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
 * @file decodeFileBlock_Http_harness.c
 * @brief Implements the proof harness for decodeFileBlock_Http function.
 */

#include <stdlib.h>

/* Http interface includes. */
#include "ota_http_private.h"


void decodeFileBlock_Http_harness()
{
    OtaErr_t err;

    uint8_t * pMessageBuffer;
    size_t messageSize;
    int32_t * pFileId;
    int32_t * pBlockId;
    int32_t * pBlockSize;
    uint8_t ** pPayload;
    size_t * pPayloadSize;

    int32_t fileId;
    int32_t blockId;
    int32_t blockSize;
    size_t payloadSize;

    /* These variables can never be NULL since they have been declared
     * statically in the decodeAndStoreDataBlock function. It is the only function that calls
     * decodeFileBlock_Http function.  */
    pFileId = &fileId;
    pBlockId = &blockId;
    pBlockSize = &blockSize;

    pPayload = ( uint8_t ** ) malloc( sizeof( char * ) );

    /* pPayload cannot point to NULL since it is always initialized in the ingestDataBlock function. */
    __CPROVER_assume( pPayload != NULL );

    *pPayload = ( char * ) malloc( messageSize * sizeof( char ) );
    pMessageBuffer = ( uint8_t * ) malloc( messageSize * sizeof( uint8_t ) );

    /* The memory address pointed by the pPayload can never be NULL since it is initialized in the
     * decodeAndStoreDataBlock function.  */
    __CPROVER_assume( *pPayload != NULL );

    pPayloadSize = &payloadSize;

    /* pMessageBuffer is an statically declared event message buffer which is passed from processDataHandler
     * to the decodeAndStoreDataBlock function. */
    __CPROVER_assume( pMessageBuffer != NULL );

    err = decodeFileBlock_Http( pMessageBuffer, messageSize, pFileId,
                                pBlockId, pBlockSize, pPayload, pPayloadSize );

    /* The function cannot return values other than OtaErrNone and OtaErrInvalidArg. */
    __CPROVER_assert( ( ( err == OtaErrNone ) || ( err == OtaErrInvalidArg ) ),
                      "Invalid function return value: Expected value should be either OtaErrNone or OtaErrInvalidArg." );

    free( *pPayload );
    free( pMessageBuffer );
    free( pPayload );
}
