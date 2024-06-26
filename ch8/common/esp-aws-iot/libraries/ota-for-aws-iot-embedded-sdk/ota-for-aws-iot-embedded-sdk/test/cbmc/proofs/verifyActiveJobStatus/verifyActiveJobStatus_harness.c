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
 * @file verifyActiveJobStatus_harness.c
 * @brief Implements the proof harness for verifyActiveJobStatus function.
 */
/*  Ota Agent includes. */
#include "ota.h"
#include "stubs.h"
#include "ota_interface_private.h"
#include <stdlib.h>
#include <string.h>

extern OtaAgentContext_t otaAgent;
extern OtaDataInterface_t otaDataInterface;
extern OtaJobParseErr_t verifyActiveJobStatus( OtaFileContext_t * pFileContext,
                                               OtaFileContext_t ** pFinalFile,
                                               bool * pUpdateJob );

void verifyActiveJobStatus_harness()
{
    OtaInterfaces_t otaInterface;
    OtaFileContext_t * pFileContext;
    OtaFileContext_t * finalFile = NULL;
    bool pUpdateJob;

    size_t jobSize;
    uint16_t updateUrlMaxSize;

    /* Havoc otaAgent and pFileContext to non-deterministically set all the bytes in
     * the structure. */
    __CPROVER_havoc_object( &otaAgent );
    __CPROVER_havoc_object( pFileContext );

    pFileContext = ( OtaFileContext_t * ) malloc( sizeof( OtaFileContext_t ) );
    __CPROVER_assume( pFileContext != NULL );

    /* Allocate memory to store the path of the url. */
    otaAgent.fileContext.pUpdateUrlPath = ( uint8_t * ) malloc( sizeof( uint8_t ) * updateUrlMaxSize );

    /* pJobName is used to store the name of the job and hence the size of the buffer cannot
     * be greater than the size of otaAgent.activeJobName. */
    pFileContext->pJobName = ( uint8_t * ) malloc( sizeof( uint8_t ) * OTA_JOB_ID_MAX_SIZE );

    /* otaAgent.fileContext is passed as the fileContext to verifyActiveJobStatus and cannot
     * have a NULL buffer. */
    pFileContext->pUpdateUrlPath = ( uint8_t * ) malloc( sizeof( uint8_t ) * updateUrlMaxSize );
    __CPROVER_assume( pFileContext->pUpdateUrlPath != NULL );

    /* Initialize job name in filecontext. */
    __CPROVER_assume( jobSize < OTA_JOB_ID_MAX_SIZE );

    if( pFileContext->pJobName != NULL )
    {
        pFileContext->pJobName[ jobSize ] = '\0';
        memset( pFileContext->pJobName, 'a', jobSize );

        if( nondet_bool() )
        {
            memcpy( otaAgent.pActiveJobName, pFileContext->pJobName, jobSize );
        }
    }

    /* To non-deterministically assume if the buffer is allocated by the user or by us. */
    if( nondet_bool() )
    {
        otaAgent.fileContext.updateUrlMaxSize = 0u;
    }
    else
    {
        otaAgent.fileContext.updateUrlMaxSize = updateUrlMaxSize;
    }

    /* CBMC preconditions. */
    otaInterface.os.mem.free = freeMemStub;
    otaInterface.pal.setPlatformImageState = setPlatformImageStateStub;
    otaInterface.pal.abort = abortPalStub;
    otaDataInterface.cleanup = cleanupStub;

    /* OtaInterfaces and the interfaces included in it cannot be NULL and they are checked
     * during the initialization of OTA specifically in the OTA_Init function. */
    otaAgent.pOtaInterface = &otaInterface;

    verifyActiveJobStatus( pFileContext, &finalFile, &pUpdateJob );

    free( pFileContext->pUpdateUrlPath );
    free( pFileContext->pJobName );
    free( pFileContext );
    free( otaAgent.fileContext.pUpdateUrlPath );
}
