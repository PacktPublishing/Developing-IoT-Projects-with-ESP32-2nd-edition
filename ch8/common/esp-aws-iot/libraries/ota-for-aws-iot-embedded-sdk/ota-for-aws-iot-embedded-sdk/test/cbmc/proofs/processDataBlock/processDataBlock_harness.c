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
 * @file processDataBlock_harness.c
 * @brief Implements the proof harness for processDataBlock function.
 */
/*  Ota Agent includes. */
#include "ota.h"
#include "stubs.h"
#include <stdlib.h>

extern OtaAgentContext_t otaAgent;
extern uint32_t processDataBlock( OtaFileContext_t * pFileContext,
                                  uint32_t uBlockIndex,
                                  uint32_t uBlockSize,
                                  OtaPalStatus_t * pCloseResult,
                                  uint8_t * pPayload );

/* Stub to validate incoming data block. */
bool validateDataBlock( const OtaFileContext_t * pFileContext,
                        uint32_t blockIndex,
                        uint32_t blockSize )
{
    bool status;

    __CPROVER_assert( pFileContext != NULL, "Error: Expected a Non-Null value for pFileContext" );

    return status;
}

void processDataBlock_harness()
{
    /* fileContext, closeResult can never be NULL as they are statically declared in ingestDataBlock
     * before the call to processDataBlock. */
    IngestResult_t result;
    OtaInterfaces_t otaInterface;
    OtaFileContext_t fileContext;
    uint32_t uBlockIndex;
    uint32_t uBlockSize;
    OtaPalStatus_t closeResult;
    uint8_t * pPayload;

    uint32_t fileBitmapSize;

    /* Havoc otaAgent and fileContext to non-deterministically set all the bytes in
     * the object. */
    __CPROVER_havoc_object( &otaAgent );
    __CPROVER_havoc_object( &fileContext );

    /* The maximum number of Blocks is defined by the OTA_MAX_BITMAP_SIZE and the size of
     * the receiver block bitmap cannot exceed that. */
    fileContext.pRxBlockBitmap = ( uint8_t * ) malloc( OTA_MAX_BLOCK_BITMAP_SIZE );
    __CPROVER_assume( fileContext.pRxBlockBitmap != NULL );
    __CPROVER_assume( uBlockIndex < ( OTA_MAX_BLOCK_BITMAP_SIZE << 3 ) );

    /* processDataBlock is called only when there are unprocessed blocks present in the
     * file context. */
    __CPROVER_assume( fileContext.blocksRemaining > 0 );
    __CPROVER_assume( pPayload != NULL );

    __CPROVER_assume( ( uBlockSize == OTA_FILE_BLOCK_SIZE ) ||
                      ( ( fileContext.blocksRemaining == 1 ) && ( uBlockSize < OTA_FILE_BLOCK_SIZE ) ) );

    /* CBMC preconditions. */
    otaInterface.pal.writeBlock = writeBlockPalStub;
    otaAgent.pOtaInterface = &otaInterface;

    result = processDataBlock( &fileContext, uBlockIndex, uBlockSize, &closeResult, pPayload );

    /* CBMC postconditions.*/
    __CPROVER_assert( ( result >= IngestResultUninitialized ) && ( result <= IngestResultDuplicate_Continue ),
                      "Error: Return value from processDataBlock should follow values of IngestResult_t enum." );

    free( fileContext.pRxBlockBitmap );
}
