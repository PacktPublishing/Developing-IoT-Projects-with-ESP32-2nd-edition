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
 * @file ingestDataBlock_harness.c
 * @brief Implements the proof harness for ingestDataBlock function.
 */
/*  Ota Agent includes. */
#include "ota.h"
#include "stubs.h"
#include <stdlib.h>

extern OtaAgentContext_t otaAgent;
extern IngestResult_t ingestDataBlock( OtaFileContext_t * pFileContext,
                                       const OtaEventData_t * pEventData,
                                       OtaPalStatus_t * pCloseResult );

IngestResult_t ingestDataBlockCleanup( OtaFileContext_t * pFileContext,
                                       OtaPalStatus_t * pCloseResult )
{
    IngestResult_t result;

    __CPROVER_assert( pFileContext != NULL,
                      "Error: Expected a non-NUll value for pFileContext" );

    __CPROVER_assert( pCloseResult != NULL,
                      "Error: Expected a non-NUll value for pCloseResult" );

    return result;
}

IngestResult_t decodeAndStoreDataBlock( OtaFileContext_t * pFileContext,
                                        const uint8_t * pRawMsg,
                                        uint32_t messageSize,
                                        uint8_t ** pPayload,
                                        uint32_t * pBlockSize,
                                        uint32_t * pBlockIndex )
{
    IngestResult_t result;

    /* pPayload, pBlockSize, pBlockIndex are initialized in ingestDataBlock before this stub
     * is called and hence cannot be NULL. pFileContext and pRawMsg are statically allocated in
     * processDataHandler before ingestDataBlock is called. */
    __CPROVER_assert( pFileContext != NULL,
                      "Error: Expected a non-NUll value for pFileContext" );
    __CPROVER_assert( pRawMsg != NULL,
                      "Error: Expected a non-NUll value for pRawMsg" );
    __CPROVER_assert( pPayload != NULL,
                      "Error: Expected a non-NUll value for pPayload" );
    __CPROVER_assert( pBlockSize != NULL,
                      "Error: Expected a non-NUll value for pBlockSize" );
    __CPROVER_assert( pBlockIndex != NULL,
                      "Error: Expected a non-NUll value for pBlockIndex" );

    *pPayload = ( uint8_t * ) malloc( 1UL << otaconfigLOG2_FILE_BLOCK_SIZE );

    return result;
}

IngestResult_t processDataBlock( OtaFileContext_t * pFileContext,
                                 uint32_t uBlockIndex,
                                 uint32_t uBlockSize,
                                 OtaPalStatus_t * pCloseResult,
                                 uint8_t * pPayload )
{
    IngestResult_t result;

    __CPROVER_assert( pFileContext != NULL,
                      "Error: Expected a non-NUll value for pFileContext" );
    __CPROVER_assert( pCloseResult != NULL,
                      "Error: Expected a non-NUll value for pCloseResult" );


    return result;
}

void ingestDataBlock_harness()
{
    OtaInterfaces_t otaInterface;
    OtaFileContext_t fileContext;
    OtaPalStatus_t closeResult;
    OtaEventData_t eventData;

    uint32_t decodeMemMaxSize;

    __CPROVER_assume( eventData.dataLength <= OTA_DATA_BLOCK_SIZE );

    /* CBMC preconditions. */

    /* Havoc otaAgent to non-deterministically set all the bytes in
     * the structure. */
    __CPROVER_havoc_object( &otaAgent );

    otaInterface.os.mem.free = freeMemStub;
    otaAgent.pOtaInterface = &otaInterface;

    ( void ) ingestDataBlock( &fileContext, &eventData, &closeResult );
}
