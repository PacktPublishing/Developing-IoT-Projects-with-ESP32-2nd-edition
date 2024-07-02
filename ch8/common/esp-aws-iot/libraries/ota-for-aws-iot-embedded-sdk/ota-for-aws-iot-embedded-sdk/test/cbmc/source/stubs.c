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
 * @file stubs.c
 * @brief Includes the definition of all the stubs required for the CBMC proofs.
 */
/*  Ota Agent includes. */
#include "ota.h"
#include "stubs.h"
#include <stdlib.h>

OtaErr_t initFileTransferStub( OtaAgentContext_t * agent )
{
    OtaErr_t err;

    __CPROVER_assert( agent != NULL,
                      "Error: OtaAgent needs to be initialized before calling initFileTransfer." );

    __CPROVER_assume( ( err >= OtaErrNone ) && ( err <= OtaErrActivateFailed ) );

    return err;
}

OtaOsStatus_t startTimerStub( OtaTimerId_t otaTimerId,
                              const char * const pTimerName,
                              const uint32_t timeout,
                              OtaTimerCallback_t callback )
{
    OtaOsStatus_t status;

    /* status must have values only from the OtaOsStatus_t enum. */
    __CPROVER_assume( ( status >= OtaOsSuccess ) && ( status <= OtaOsTimerDeleteFailed ) );

    __CPROVER_assert( ( otaTimerId == OtaSelfTestTimer ) || ( otaTimerId == OtaRequestTimer ),
                      "Error: Expected otaTimerId to be either OtaSelfTestTimer or OtaRequestTimer." );

    __CPROVER_assert( pTimerName != NULL, "Error: TimerName cannot be NULL" );

    __CPROVER_assert( callback != NULL, "Error: callback should be pointing to a function." );

    return status;
}

OtaOsStatus_t stopTimerStub( OtaTimerId_t otaTimerId )
{
    OtaOsStatus_t status;

    /* status must have values only from the OtaOsStatus_t enum. */
    __CPROVER_assume( ( status >= OtaOsSuccess ) && ( status <= OtaOsTimerDeleteFailed ) );

    __CPROVER_assert( ( otaTimerId == OtaSelfTestTimer ) || ( otaTimerId == OtaRequestTimer ),
                      "Error: Expected otaTimerId to be either OtaSelfTestTimer or OtaRequestTimer." );

    return status;
}

OtaPalImageState_t getPlatformImageStateStub( OtaFileContext_t * const pFileContext )
{
    OtaPalImageState_t state;

    /* state must have values of OtaPalImageState_t enum. */
    __CPROVER_assume( ( state >= OtaPalImageStateUnknown ) && ( state <= OtaPalImageStateInvalid ) );

    __CPROVER_assert( pFileContext != NULL,
                      "Error: pFileContext in the otaAgent is statically initialized and hence cannot be NULL." );

    return state;
}

void otaAppCallback( OtaJobEvent_t eEvent,
                     const void * pData )
{
}

OtaPalStatus_t resetPalStub( OtaFileContext_t * const pFileContext )
{
    OtaPalStatus_t status;

    /* status must have values only from the OtaPalStatus_t enum. */
    __CPROVER_assume( ( status >= 0 ) && ( status <= UINT32_MAX ) );

    __CPROVER_assert( pFileContext != NULL, "Error: Expected pFileContext to be not NULL" );

    return status;
}

OtaErr_t setImageStateWithReason( OtaImageState_t stateToSet,
                                  uint32_t reasonToSet )
{
    OtaErr_t err;

    /* err must have values only from the OtaErr_t enum. */
    __CPROVER_assume( ( err >= OtaErrNone ) && ( err <= OtaErrActivateFailed ) );

    return err;
}

OtaErr_t requestJobStub( OtaAgentContext_t * pAgentCtx )
{
    OtaErr_t err;

    /* err must have values only from the OtaErr_t enum. */
    __CPROVER_assume( ( err >= OtaErrNone ) && ( err <= OtaErrActivateFailed ) );

    __CPROVER_assert( pAgentCtx != NULL,
                      "Error: Agent Context should be defined before calling the function." );

    return err;
}

OtaOsStatus_t recvEventStub( OtaEventContext_t * pEventCtx,
                             void * pEventMsg,
                             uint32_t timeout )
{
    OtaEventMsg_t eventMsg;
    OtaOsStatus_t status;

    pEventMsg = &eventMsg;

    /* status must have values only from the OtaOsStatus_t enum. */
    __CPROVER_assume( ( status >= OtaOsSuccess ) && ( status <= OtaOsTimerDeleteFailed ) );

    return status;
}

OtaErr_t updateJobStatusStub( OtaAgentContext_t * pAgentCtx,
                              OtaJobStatus_t status,
                              int32_t reason,
                              int32_t subReason )
{
    OtaErr_t err;

    /* err must have values only from the OtaErr_t enum. */
    __CPROVER_assume( ( err >= OtaErrNone ) && ( err <= OtaErrActivateFailed ) );

    __CPROVER_assert( pAgentCtx != NULL, "Error: Agent context can never be NULL." );

    return err;
}

OtaOsStatus_t sendEventStub( OtaEventContext_t * pEventCtx,
                             const void * pEventMsg,
                             unsigned int timeout )
{
    OtaOsStatus_t status;

    /* pEventMsg is statically initialized before it is passed to the send
     * function in OTA_SignalEvent. */
    __CPROVER_assert( pEventMsg != NULL,
                      "Error: Expected a non-NULL event Context." );

    /* status must have values only from the OtaOsStatus_t enum. */
    __CPROVER_assume( ( status >= OtaOsSuccess ) && ( status <= OtaOsTimerDeleteFailed ) );

    return status;
}

OtaErr_t cleanupStub( OtaAgentContext_t * pAgentCtx )
{
    OtaErr_t err;

    /* err must have values only from the OtaErr_t enum. */
    __CPROVER_assume( ( err >= OtaErrNone ) && ( err <= OtaErrActivateFailed ) );

    __CPROVER_assert( pAgentCtx != NULL, "Error: Agent context can never be NULL." );

    return err;
}

OtaPalStatus_t setPlatformImageStateStub( OtaFileContext_t * const pFileContext,
                                          OtaImageState_t eState )
{
    OtaPalStatus_t status;

    /* status must have values of OtaPalStatus_t. */
    __CPROVER_assume( status <= UINT32_MAX );

    __CPROVER_assert( pFileContext != NULL,
                      "Error: pFileContext in the otaAgent is statically initialized and hence cannot be NULL." );

    return status;
}

OtaPalStatus_t abortPalStub( OtaFileContext_t * const pFileContext )
{
    OtaPalStatus_t status;

    /* status must have values of OtaPalStatus_t. */
    __CPROVER_assume( status <= UINT32_MAX );

    __CPROVER_assert( pFileContext != NULL,
                      "Error: pFileContext in the otaAgent is statically initialized and hence cannot be NULL." );

    return status;
}


void * mallocMemStub( size_t size )
{
    void * ptr;

    ptr = ( void * ) malloc( size );

    return ptr;
}

OtaErr_t decodeFileBlockStub( const uint8_t * pMessageBuffer,
                              size_t messageSize,
                              int32_t * pFileId,
                              int32_t * pBlockId,
                              int32_t * pBlockSize,
                              uint8_t ** pPayload,
                              size_t * pPayloadSize )
{
    OtaErr_t err;

    /* err must have values only from the OtaErr_t enum. */
    __CPROVER_assume( ( err >= OtaErrNone ) && ( err <= OtaErrActivateFailed ) );

    /* Pre-conditions.
     * pPayload and  pMessageBuffer are initialized in the ingestDataBlock before passing it to
     * decodeAndStoreDataBlock which in turn calls decodeFileBlock Function and hence cannot
     * be NULL.
     * pPayloadSize, pFileId, pBlockId, pBlockSize are statically initialized in decodeAndStoreDataBlock
     * before calling this stub and hence cannot be NULL.
     */
    __CPROVER_assert( pPayload != NULL, "Invalid pPayload value: pPayload cannot be NULL." );
    __CPROVER_assert( pMessageBuffer != NULL, "Invalid pMessageBuffer value: pMessageBuffer cannot be NULL." );
    __CPROVER_assert( pPayloadSize != NULL, "Invalid pPayloadSize value: pPayloadSize cannot be NULL." );
    __CPROVER_assert( pFileId != NULL, "Invalid pFileId value: pFileId cannot be NULL." );
    __CPROVER_assert( pBlockId != NULL, "Invalid pBlockId value: pBlockId cannot be NULL." );
    __CPROVER_assert( pBlockSize != NULL, "Invalid pBlockSize value: pBlockSize cannot be NULL." );

    return err;
}

void freeMemStub( void * ptr )
{
    free( ptr );
}

int16_t writeBlockPalStub( OtaFileContext_t * const pFileContext,
                           uint32_t offset,
                           uint8_t * const pData,
                           uint32_t blockSize )
{
    int16_t bytesWritten;

    __CPROVER_assert( pFileContext != NULL, "Error: Expected a Non-Null value for pFileContext" );
    __CPROVER_assert( pData != NULL, "Error: Expected a Non-Null value for pData" );

    /* bytesWritten must be negative (fail) or equal to blockSize (pass). */
    __CPROVER_assume( bytesWritten < 0 || ( uint32_t ) bytesWritten == blockSize );

    return bytesWritten;
}

OtaPalStatus_t closeFilePalStub( OtaFileContext_t * const pFileContext )
{
    OtaPalStatus_t status;

    /* status must have values of OtaPalStatus_t. */
    __CPROVER_assume( status <= UINT32_MAX );

    __CPROVER_assert( pFileContext != NULL, "Error: Expected a Non-Null value for pFileContext" );

    return status;
}

OtaPalStatus_t createFilePalStub( OtaFileContext_t * const pFileContext )
{
    OtaPalStatus_t status;

    /* status must have values of OtaPalStatus_t. */
    __CPROVER_assume( status <= UINT32_MAX );

    __CPROVER_assert( pFileContext != NULL, "Error: Expected a Non-Null value for pFileContext" );

    return status;
}

OtaErr_t requestFileBlockStub( OtaAgentContext_t * pAgentCtx )
{
    OtaErr_t err;

    __CPROVER_assert( pAgentCtx != NULL, "Error: Expected a non-NULL value for the agent." );

    return err;
}

OtaOsStatus_t deleteTimerStub( OtaTimerId_t otaTimerId )
{
    OtaOsStatus_t status;

    /* status must have values only from the OtaOsStatus_t enum. */
    __CPROVER_assume( ( status >= OtaOsSuccess ) && ( status <= OtaOsTimerDeleteFailed ) );

    __CPROVER_assert( ( otaTimerId == OtaSelfTestTimer ) || ( otaTimerId == OtaRequestTimer ),
                      "Error: Expected otaTimerId to be either OtaSelfTestTimer or OtaRequestTimer." );

    return status;
}
