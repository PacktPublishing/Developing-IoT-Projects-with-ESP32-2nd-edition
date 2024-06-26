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
 * @file decodeAndStoreDataBlock_harness.c
 * @brief Implements the proof harness for decodeAndStoreDataBlock function.
 */
/*  Ota Agent includes. */
#include "ota.h"
#include "ota_interface_private.h"
#include "stubs.h"
#include <stdlib.h>

extern OtaAgentContext_t otaAgent;
extern OtaDataInterface_t otaDataInterface;
extern IngestResult_t decodeAndStoreDataBlock( OtaFileContext_t * pFileContext,
                                               const uint8_t * pRawMsg,
                                               uint32_t messageSize,
                                               uint8_t ** pPayload,
                                               uint32_t * pBlockSize,
                                               uint32_t * pBlockIndex );

void decodeAndStoreDataBlock_harness()
{
    /* fileContext is initialized to otaAgent.pFileContext which is statically defined in ota.c and
     * hence can never be NULL. */
    OtaInterfaces_t otaInterface;
    OtaFileContext_t fileContext;
    uint8_t pRawMsg[ OTA_DATA_BLOCK_SIZE ];
    uint32_t msgSize;
    uint8_t * pPayload = NULL;
    uint32_t blockSize;
    uint32_t blockIndex;
    IngestResult_t result;

    /* Pre-conditions. */

    /* Havoc otaAgent to non-deterministically set all the bytes in
     * the structure. */
    __CPROVER_havoc_object( &otaAgent );

    otaInterface.os.timer.start = startTimerStub;
    otaInterface.os.mem.malloc = mallocMemStub;

    otaDataInterface.decodeFileBlock = decodeFileBlockStub;

    /* otaAgent.pOtaInterface can never be NULL as it is always checked at the start of the OTA
     * Agent specifically in receiveAndProcessOTAEvent function.*/
    otaAgent.pOtaInterface = &otaInterface;

    if( otaAgent.fileContext.decodeMemMaxSize != 0u )
    {
        otaAgent.fileContext.pDecodeMem = ( uint8_t * ) malloc( 1UL << otaconfigLOG2_FILE_BLOCK_SIZE );
    }

    result = decodeAndStoreDataBlock( &fileContext, pRawMsg, msgSize, &pPayload, &blockSize, &blockIndex );

    __CPROVER_assert( ( result >= IngestResultUninitialized ) &&
                      ( result <= IngestResultDuplicate_Continue ),
                      "Invalid return value from decodeAndStoreDataBlock:Expected value should be from IngestResult_t enum." );

    if( pPayload != NULL )
    {
        free( pPayload );
    }
}
