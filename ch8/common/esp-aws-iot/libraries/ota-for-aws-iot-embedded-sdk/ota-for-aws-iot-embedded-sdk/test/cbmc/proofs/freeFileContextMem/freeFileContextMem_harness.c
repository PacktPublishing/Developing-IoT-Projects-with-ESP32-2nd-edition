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
 * @file freeFileContextMem_harness.c
 * @brief Implements the proof harness for freeFileContextMem function.
 */

#include "ota.h"
#include "stubs.h"
#include <stdlib.h>

extern OtaAgentContext_t otaAgent;
extern void freeFileContextMem( OtaFileContext_t * const pFileContext );

void freeFileContextMem_harness()
{
    OtaInterfaces_t otaInterface;
    OtaFileContext_t fileContext;
    uint16_t filePathMaxSize;
    uint16_t certFilePathMaxSize;
    uint16_t streamNameMaxSize;
    uint16_t blockBitmapMaxSize;
    uint16_t updateUrlMaxSize;
    uint16_t authSchemeMaxSize;

    fileContext.pFilePath = ( uint8_t * ) malloc( filePathMaxSize * sizeof( uint8_t ) );
    fileContext.pCertFilepath = ( uint8_t * ) malloc( certFilePathMaxSize * sizeof( uint8_t ) );
    fileContext.pStreamName = ( uint8_t * ) malloc( streamNameMaxSize * sizeof( uint8_t ) );
    fileContext.pRxBlockBitmap = ( uint8_t * ) malloc( blockBitmapMaxSize * sizeof( uint8_t ) );
    fileContext.pUpdateUrlPath = ( uint8_t * ) malloc( updateUrlMaxSize * sizeof( uint8_t ) );
    fileContext.pAuthScheme = ( uint8_t * ) malloc( authSchemeMaxSize * sizeof( uint8_t ) );

    /* Non-deterministically set the size field to indicate if the buffer is user or dynamically
     * allocated. */
    if( nondet_bool() )
    {
        fileContext.filePathMaxSize = filePathMaxSize;
    }
    else
    {
        fileContext.filePathMaxSize = 0u;
    }

    if( nondet_bool() )
    {
        fileContext.certFilePathMaxSize = certFilePathMaxSize;
    }
    else
    {
        fileContext.certFilePathMaxSize = 0u;
    }

    if( nondet_bool() )
    {
        fileContext.streamNameMaxSize = streamNameMaxSize;
    }
    else
    {
        fileContext.streamNameMaxSize = 0u;
    }

    if( nondet_bool() )
    {
        fileContext.blockBitmapMaxSize = blockBitmapMaxSize;
    }
    else
    {
        fileContext.blockBitmapMaxSize = 0u;
    }

    if( nondet_bool() )
    {
        fileContext.updateUrlMaxSize = updateUrlMaxSize;
    }
    else
    {
        fileContext.updateUrlMaxSize = 0u;
    }

    if( nondet_bool() )
    {
        fileContext.authSchemeMaxSize = authSchemeMaxSize;
    }
    else
    {
        fileContext.authSchemeMaxSize = 0u;
    }

    /* CBMC pre-conditions. */
    otaInterface.os.mem.free = freeMemStub;
    otaAgent.pOtaInterface = &otaInterface;

    freeFileContextMem( &fileContext );

    /* Free memory allocated for the buffers. */
    if( fileContext.pFilePath != NULL )
    {
        free( fileContext.pFilePath );
    }

    if( fileContext.pCertFilepath != NULL )
    {
        free( fileContext.pCertFilepath );
    }

    if( fileContext.pStreamName != NULL )
    {
        free( fileContext.pStreamName );
    }

    if( fileContext.pRxBlockBitmap != NULL )
    {
        free( fileContext.pRxBlockBitmap );
    }

    if( fileContext.pUpdateUrlPath != NULL )
    {
        free( fileContext.pUpdateUrlPath );
    }

    if( fileContext.pAuthScheme != NULL )
    {
        free( fileContext.pAuthScheme );
    }
}
