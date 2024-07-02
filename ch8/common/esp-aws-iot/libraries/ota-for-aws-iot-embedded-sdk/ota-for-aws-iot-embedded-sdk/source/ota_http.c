/*
 * AWS IoT Over-the-air Update v3.4.0
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * @file ota_http.c
 * @brief Data transfer over HTTP routines.
 */

/* Standard library include. */
#include <string.h>
#include <stdio.h>
#include <assert.h>

/* OTA includes. */
#include "ota.h"
#include "ota_private.h"
#include "ota_http_private.h"

/**
 * @brief Track the current block for HTTP requests
 *
 */
static uint32_t currBlock;

/*
 * Init file transfer by initializing the http module with the pre-signed url.
 */
OtaErr_t initFileTransfer_Http( const OtaAgentContext_t * pAgentCtx )
{
    OtaHttpStatus_t httpStatus = OtaHttpSuccess;
    char * pURL = NULL;
    const OtaFileContext_t * fileContext = NULL;

    LogDebug( ( "Invoking initFileTransfer_Http" ) );
    assert( ( pAgentCtx != NULL ) && ( pAgentCtx->pOtaInterface != NULL ) && ( pAgentCtx->pOtaInterface->http.init != NULL ) );

    /* File context from OTA agent. */
    fileContext = &( pAgentCtx->fileContext );

    /* Get pre-signed URL from pAgentCtx. */
    pURL = ( char * ) fileContext->pUpdateUrlPath;

    /* Connect to the HTTP server and initialize download information. */
    httpStatus = pAgentCtx->pOtaInterface->http.init( pURL );

    if( httpStatus != OtaHttpSuccess )
    {
        LogError( ( "Error occured while initializing http:"
                    "OtaHttpStatus_t=%s"
                    , OTA_HTTP_strerror( httpStatus ) ) );
    }

    return ( httpStatus == OtaHttpSuccess ) ? OtaErrNone : OtaErrInitFileTransferFailed;
}

/*
 * Check for next available OTA job from the job service.
 */
/* MISRA Ref 8.13.1 [Const qualified types] */
/* More details at: https://github.com/aws/ota-for-aws-iot-embedded-sdk/blob/main/MISRA.md#rule-813 */
/* coverity[misra_c_2012_rule_8_13_violation] */
OtaErr_t requestDataBlock_Http( OtaAgentContext_t * pAgentCtx )
{
    OtaHttpStatus_t httpStatus = OtaHttpSuccess;

    /* Values for the "Range" field in HTTP header. */
    uint32_t rangeStart = 0;
    uint32_t rangeEnd = 0;

    const OtaFileContext_t * fileContext;

    assert( ( pAgentCtx != NULL ) && ( pAgentCtx->pOtaInterface != NULL ) && ( pAgentCtx->pOtaInterface->http.request != NULL ) );
    fileContext = &( pAgentCtx->fileContext );
    LogDebug( ( "Invoking requestDataBlock_Http" ) );
    /* fileContext   */

    /* Calculate ranges. */
    rangeStart = currBlock * OTA_FILE_BLOCK_SIZE;

    if( fileContext->blocksRemaining == 1U )
    {
        rangeEnd = fileContext->fileSize - 1U;
    }
    else
    {
        rangeEnd = rangeStart + OTA_FILE_BLOCK_SIZE - 1U;
    }

    /* Request file data over HTTP using the rangeStart and rangeEnd. */
    httpStatus = pAgentCtx->pOtaInterface->http.request( rangeStart, rangeEnd );

    if( httpStatus != OtaHttpSuccess )
    {
        LogError( ( "Error occured while requesting data block:"
                    "OtaHttpStatus_t=%s"
                    , OTA_HTTP_strerror( httpStatus ) ) );
    }

    return ( httpStatus == OtaHttpSuccess ) ? OtaErrNone : OtaErrRequestFileBlockFailed;
}

/*
 * HTTP file block does not need to decode the block, only increment
 * number of blocks received.
 */
OtaErr_t decodeFileBlock_Http( const uint8_t * pMessageBuffer,
                               size_t messageSize,
                               int32_t * pFileId,
                               int32_t * pBlockId,
                               int32_t * pBlockSize,
                               uint8_t * const * pPayload,
                               size_t * pPayloadSize )
{
    OtaErr_t err = OtaErrNone;

    assert( ( pMessageBuffer != NULL ) && ( pFileId != NULL ) && ( pBlockId != NULL ) &&
            ( pBlockSize != NULL ) && ( pPayload != NULL ) && ( pPayloadSize != NULL ) );

    if( messageSize > OTA_FILE_BLOCK_SIZE )
    {
        LogError( ( "Incoming file block size %d larger than block size %d.",
                    ( int ) messageSize, ( int ) OTA_FILE_BLOCK_SIZE ) );
        err = OtaErrInvalidArg;
    }
    else
    {
        *pFileId = 0;
        *pBlockId = ( int32_t ) currBlock;
        *pBlockSize = ( int32_t ) messageSize;

        /* The data received over HTTP does not require any decoding. */
        ( void ) memcpy( *pPayload, pMessageBuffer, messageSize );

        *pPayloadSize = messageSize;

        /* Current block is processed, set the file block to next. */
        currBlock++;
    }

    return err;
}

/*
 * Perform any cleanup operations required for data plane.
 */
OtaErr_t cleanupData_Http( const OtaAgentContext_t * pAgentCtx )
{
    OtaHttpStatus_t httpStatus = OtaHttpSuccess;

    assert( ( pAgentCtx != NULL ) && ( pAgentCtx->pOtaInterface != NULL ) && ( pAgentCtx->pOtaInterface->http.deinit != NULL ) );

    httpStatus = pAgentCtx->pOtaInterface->http.deinit();

    /* Reset currBlock. */
    currBlock = 0;

    return ( httpStatus == OtaHttpSuccess ) ? OtaErrNone : OtaErrCleanupDataFailed;
}

const char * OTA_HTTP_strerror( OtaHttpStatus_t status )
{
    const char * str = NULL;

    switch( status )
    {
        case OtaHttpSuccess:
            str = "OtaHttpSuccess";
            break;

        case OtaHttpInitFailed:
            str = "OtaHttpInitFailed";
            break;

        case OtaHttpDeinitFailed:
            str = "OtaHttpDeinitFailed";
            break;

        case OtaHttpRequestFailed:
            str = "OtaHttpRequestFailed";
            break;

        default:
            str = "InvalidErrorCode";
            break;
    }

    return str;
}
