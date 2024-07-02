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
 * @file ingestDataBlockCleanup_harness.c
 * @brief Implements the proof harness for ingestDataBlockCleanup function.
 */
/*  Ota Agent includes. */
#include "ota.h"
#include "stubs.h"
#include <stdlib.h>

extern OtaAgentContext_t otaAgent;
extern IngestResult_t ingestDataBlockCleanup( OtaFileContext_t * pFileContext,
                                              OtaPalStatus_t * pCloseResult );

void ingestDataBlockCleanup_harness()
{
    IngestResult_t result;
    OtaFileContext_t fileContext;
    OtaPalStatus_t closeResult;
    OtaInterfaces_t otaInterface;

    /* Havoc otaAgent and fileContext to non-deterministically set the bytes
     * in the object. */
    __CPROVER_havoc_object( &fileContext );
    __CPROVER_havoc_object( &otaAgent );

    fileContext.pRxBlockBitmap = ( uint8_t * ) malloc( OTA_MAX_BLOCK_BITMAP_SIZE );

    /* Preconditions. */
    otaInterface.os.timer.stop = stopTimerStub;
    otaInterface.pal.closeFile = closeFilePalStub;
    otaInterface.os.mem.free = freeMemStub;

    /* otaAgent.pOtaInterface can never be NULL as it is always checked at the start of the OTA
     * Agent specifically in receiveAndProcessOTAEvent function.*/
    otaAgent.pOtaInterface = &otaInterface;

    result = ingestDataBlockCleanup( &fileContext, &closeResult );

    /* result can only have values of IngestResult_t enum. */
    __CPROVER_assert( ( result >= IngestResultUninitialized ) && ( result <= IngestResultDuplicate_Continue ),
                      "Error: Return value from ingestDataBlockCleanup should follow values of IngestResult_t enum." );

    if( fileContext.blockBitmapMaxSize != 0u )
    {
        free( fileContext.pRxBlockBitmap );
    }
}
