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
 * @file processDataHandler_harness.c
 * @brief Implements the proof harness for processDataHandler function.
 */
/* Include headers for ota agent. */
#include "ota.h"
#include "ota_interface_private.h"
#include <stdlib.h>

extern OtaAgentContext_t otaAgent;
extern OtaControlInterface_t otaControlInterface;
extern OtaErr_t processDataHandler( const OtaEventData_t * pEventData );

/* Stub for ingestDataBlock. */
IngestResult_t ingestDataBlock( OtaFileContext_t * pFileContext,
                                const OtaEventData_t * pEventData,
                                OtaPalStatus_t * pCloseResult )
{
    IngestResult_t result;
    OtaPalStatus_t status;

    __CPROVER_assert( pFileContext != NULL, "Error: pFileContext cannot be NULL" );
    __CPROVER_assert( pCloseResult != NULL, "Error: pCloseResult cannot be NULL" );

    return result;
}

/* Stub to update the job status. */
OtaErr_t updateStatus( OtaAgentContext_t * pAgentCtx,
                       OtaJobStatus_t status,
                       int32_t reason,
                       int32_t subReason )
{
    OtaErr_t err;

    __CPROVER_assert( pAgentCtx != NULL,
                      "Error: Ota Agent has to be defined before calling updateJobStatus function." );

    return err;
}

/* Stub for callback function */
void otaAppCallback( OtaJobEvent_t eEvent,
                     const void * pData )
{
}

/* Stub for platform specific interface. */
OtaPalStatus_t setImageState( OtaFileContext_t * const pFileContext,
                              OtaImageState_t eState )
{
    OtaPalStatus_t status;

    __CPROVER_assert( pFileContext != NULL,
                      "Error: pFileContext is statically defined in otaAgent struct and cannot be NULL." );

    return status;
}

/* Stub to start the timer event. */
OtaOsStatus_t start( OtaTimerId_t otaTimerId,
                     const char * const pTimerName,
                     const uint32_t timeout,
                     OtaTimerCallback_t callback )
{
    OtaOsStatus_t status;

    __CPROVER_assert( ( otaTimerId != OtaRequestTimer ) || ( otaTimerId != OtaSelfTestTimer ),
                      "Error: Invalid otaTimerId type. Expected OtaRequestTimer or OtaSelfTestTimer" );

    return status;
}

void processDataHandler_harness()
{
    OtaErr_t err;
    OtaEventData_t * pEventData;
    OtaInterfaces_t otaInterface;
    size_t idx;

    pEventData = ( OtaEventData_t * ) malloc( sizeof( OtaEventData_t ) );

    /* Havoc otaAgent. */
    __CPROVER_havoc_object( &otaAgent );

    /* The fileType is limited by the service to not exceed INT32_MAX */
    __CPROVER_assume( otaAgent.fileContext.fileType <= INT32_MAX );

    /* Initialize the interface functions. */
    otaInterface.pal.setPlatformImageState = setImageState;
    otaInterface.os.timer.start = start;

    /* Update the control Interface functions. */
    otaControlInterface.updateJobStatus = updateStatus;

    /* Initialize the app callback.*/
    otaAgent.OtaAppCallback = otaAppCallback;

    /* To set the size of the pActiveJobName within the bounded limits. */
    __CPROVER_assume( idx < OTA_JOB_ID_MAX_SIZE );
    otaAgent.pActiveJobName[ idx ] = '\0';

    otaAgent.pOtaInterface = &otaInterface;

    processDataHandler( pEventData );

    free( pEventData );
}
