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
 * @file stubs.h
 * @brief Includes the declaration of all the stubs required in the CBMC proofs.
 */

/* Stub for initFileTransfer function. */
OtaErr_t initFileTransferStub( OtaAgentContext_t * agent );

/* Stub for Timer Start interface. */
OtaOsStatus_t startTimerStub( OtaTimerId_t otaTimerId,
                              const char * const pTimerName,
                              const uint32_t timeout,
                              OtaTimerCallback_t callback );

/* Stub for Timer Stop interface. */
OtaOsStatus_t stopTimerStub( OtaTimerId_t otaTimerId );

/* Stub to get the platform state from OTA PAL layer. */
OtaPalImageState_t getPlatformImageStateStub( OtaFileContext_t * const pFileContext );

/* Stub for callback from the OTA agent. */
void otaAppCallbackStub( OtaJobEvent_t eEvent,
                         const void * pData );

/* Stub to reset the OTA PAL layer. */
OtaPalStatus_t resetPalStub( OtaFileContext_t * const pFileContext );

/* Stub to set the Image State. */
OtaErr_t setImageStateWithReason( OtaImageState_t stateToSet,
                                  uint32_t reasonToSet );

/* Stub to request the next available job from job service. */
OtaErr_t requestJobStub( OtaAgentContext_t * pAgentCtx );

/* Stub to receive Events .*/
OtaOsStatus_t recvEventStub( OtaEventContext_t * pEventCtx,
                             void * pEventMsg,
                             uint32_t timeout );

/* Stub to update the job status. */
OtaErr_t updateJobStatusStub( OtaAgentContext_t * pAgentCtx,
                              OtaJobStatus_t status,
                              int32_t reason,
                              int32_t subReason );

/* Stub to send Event updates. */
OtaOsStatus_t sendEventStub( OtaEventContext_t * pEventCtx,
                             const void * pEventMsg,
                             unsigned int timeout );

/* Stub to cleanup Data and Control plane. */
OtaErr_t cleanupStub( OtaAgentContext_t * pAgentCtx );

/* Stub to set the state of the platform. */
OtaPalStatus_t setPlatformImageStateStub( OtaFileContext_t * const pFileContext,
                                          OtaImageState_t eState );

/* Stub to abort an OTA transfer. */
OtaPalStatus_t abortPalStub( OtaFileContext_t * const pFileContext );

/* Stub to allocate memory. */
void * mallocMemStub( size_t size );

/* Stub to decode file block. */
OtaErr_t decodeFileBlockStub( const uint8_t * pMessageBuffer,
                              size_t messageSize,
                              int32_t * pFileId,
                              int32_t * pBlockId,
                              int32_t * pBlockSize,
                              uint8_t ** pPayload,
                              size_t * pPayloadSize );

/* Stub to free memory. */
void freeMemStub( void * ptr );

/* Stub to write a block. */
int16_t writeBlockPalStub( OtaFileContext_t * const pFileContext,
                           uint32_t offset,
                           uint8_t * const pData,
                           uint32_t blockSize );

/* Stub to close a file. */
OtaPalStatus_t closeFilePalStub( OtaFileContext_t * const pFileContext );

/* Stub to create a file. */
OtaPalStatus_t createFilePalStub( OtaFileContext_t * const pFileContext );

/* Stub to request a fileblock from the Data plane. */
OtaErr_t requestFileBlockStub( OtaAgentContext_t * pAgentCtx );

/* Stub to delete timer. */
OtaOsStatus_t deleteTimerStub( OtaTimerId_t otaTimerId );
