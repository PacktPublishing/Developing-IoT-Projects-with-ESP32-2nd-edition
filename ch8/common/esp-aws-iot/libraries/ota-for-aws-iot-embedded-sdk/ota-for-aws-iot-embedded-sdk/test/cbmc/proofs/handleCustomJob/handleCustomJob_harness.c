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
 * @file handleCustomJob_harness.c
 * @brief Implements the proof harness for handleCustomJob function.
 */
/*  Ota Agent includes. */
#include "ota.h"
#include "stubs.h"
#include "ota_interface_private.h"
#include <stdlib.h>
#include <string.h>
#include "core_json.h"

extern OtaAgentContext_t otaAgent;
extern OtaControlInterface_t otaControlInterface;
extern OtaJobParseErr_t handleCustomJob( const char * pJson,
                                         uint32_t messageLength );

/* Pointer to initialize the jobId buffer in the job document structure. */
const uint8_t * jobId;

/* Stub to search for params in a JSON job doc. */
JSONStatus_t JSON_SearchConst( const char * buf,
                               size_t max,
                               const char * query,
                               size_t queryLength,
                               const char ** outValue,
                               size_t * outValueLength,
                               JSONTypes_t * outType )
{
    JSONStatus_t status;
    size_t jobIdLength;

    __CPROVER_assert( outValueLength != NULL,
                      "Invalid val: outValueLength cannot be NULL." );

    jobId = ( const uint8_t * ) malloc( sizeof( uint8_t ) * jobIdLength );

    /* jobId cannot be NULL as it is statically initialize in the handleCustomJob function.*/
    __CPROVER_assume( jobId != NULL );

    *outValue = jobId;
    *outValueLength = jobIdLength;

    __CPROVER_assume( ( status >= JSONPartial ) && ( status <= JSONBadParameter ) );
    return status;
}

/* Stub which changes the parseErr in the job document structure. */
void otaAppCallbackStub( OtaJobEvent_t eEvent,
                         const void * pData )
{
    OtaJobDocument_t * jobDoc = ( OtaJobDocument_t * ) pData;
    OtaJobParseErr_t parseErr;

    __CPROVER_assume( ( parseErr <= OtaJobParseErrNoActiveJobs ) && ( parseErr >= OtaJobParseErrUnknown ) );

    jobDoc->parseErr = parseErr;
}

void handleCustomJob_harness()
{
    const char * pJson;
    uint32_t messageLength;
    size_t pJsonSize;

    pJson = ( const char * ) malloc( sizeof( char ) * pJsonSize );

    /* The size of the message present in the pJson buffer should always be
     * less than the size of the buffer. */
    __CPROVER_assume( messageLength < pJsonSize );

    /* Preconditions. */
    otaAgent.OtaAppCallback = otaAppCallbackStub;
    otaControlInterface.updateJobStatus = updateJobStatusStub;

    handleCustomJob( pJson, messageLength );

    free( pJson );
    free( jobId );
}
