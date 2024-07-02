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
 * @file getFileContextFromJob_harness.c
 * @brief Implements the proof harness for getFileContextFromJob function.
 */
/*  Ota Agent includes. */
#include "ota.h"
#include "stubs.h"
#include <stdlib.h>
#include <string.h>
#include "ota_interface_private.h"

OtaFileContext_t fileContext;

extern OtaAgentContext_t otaAgent;
extern OtaFileContext_t * getFileContextFromJob( const char * pRawMsg,
                                                 uint32_t messageLength );

OtaFileContext_t * parseJobDoc( const JsonDocParam_t * pJsonExpectedParams,
                                uint16_t numJobParams,
                                const char * pJson,
                                uint32_t messageLength,
                                bool * pUpdateJob )
{
    uint32_t fileSize;
    bool update;

    /* pJsonExpectedParams is expected to be a global structure. pUpdateJob is statically declared in
     * getFileContextFromJob before passing it to parseJobDoc hence cannot be NULL. */
    __CPROVER_assert( pJsonExpectedParams != NULL,
                      "Error: Expected a non-NULL value for pJsonExpectedParams. " );

    __CPROVER_assert( pUpdateJob != NULL,
                      "Error: Expected a non-NULL value for pUpdateJob. " );

    *pUpdateJob = update;

    /* The maximum and the minimum size of the downloaded fileSize allowed to
     * avoid buffer overflow. */
    __CPROVER_assume( ( fileSize > 0u ) && ( fileSize < OTA_MAX_FILE_SIZE ) );

    fileContext.pRxBlockBitmap = ( uint8_t * ) malloc( sizeof( uint8_t ) * OTA_MAX_BLOCK_BITMAP_SIZE );

    /* To non-deterministically select if the pRxBlockBitmap buffer was initialized by the
     * user or not. */
    if( nondet_bool() )
    {
        fileContext.blockBitmapMaxSize = OTA_MAX_BLOCK_BITMAP_SIZE;
        __CPROVER_assume( fileContext.pRxBlockBitmap != NULL );
    }
    else
    {
        fileContext.blockBitmapMaxSize = 0u;
    }

    return &fileContext;
}

void getFileContextFromJob_harness()
{
    OtaFileContext_t * pFileContext;
    OtaInterfaces_t otaInterface;
    char rawMsg[ OTA_DATA_BLOCK_SIZE ];
    uint32_t messageLength;

    size_t jobNameSize;

    /* Pre-conditions. */
    __CPROVER_havoc_object( &otaAgent );

    __CPROVER_assume( messageLength < OTA_DATA_BLOCK_SIZE );

    /* The length of jobName string cannot exceed the size of buffer allocated to it. */
    __CPROVER_assume( jobNameSize < OTA_JOB_ID_MAX_SIZE );
    otaAgent.pActiveJobName[ jobNameSize ] = '\0';
    memset( otaAgent.pActiveJobName, 'a', jobNameSize );

    otaInterface.pal.getPlatformImageState = getPlatformImageStateStub;
    otaInterface.os.mem.free = freeMemStub;
    otaInterface.os.mem.malloc = mallocMemStub;
    otaInterface.pal.createFile = createFilePalStub;

    /* otaAgent.pOtaInterface can never be NULL as it is always checked at the start of the OTA
     * Agent specifically in receiveAndProcessOTAEvent function.*/
    otaAgent.pOtaInterface = &otaInterface;

    ( void ) getFileContextFromJob( &rawMsg, messageLength );
}
