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
 * @file handleJobParsingError_harness.c
 * @brief Implements the proof harness for handleJobParsingError function.
 */
/*  Ota Agent includes. */
#include "ota.h"
#include "stubs.h"
#include "ota_interface_private.h"

extern OtaAgentContext_t otaAgent;
extern OtaControlInterface_t otaControlInterface;
extern void handleJobParsingError( const OtaFileContext_t * pFileContext,
                                   OtaJobParseErr_t err );

void handleJobParsingError_harness()
{
    OtaJobParseErr_t err;
    OtaFileContext_t fileContext; /* pFileContext can never be NULL as it is a field of statically declared otaAgent struct. */
    size_t jobNameIdx;
    uint8_t jobNameBuffer[ OTA_JOB_ID_MAX_SIZE ];

    /* handleJobParsingError is only called with otaAgent.fileContext as it's argument.
     * otaAgent.fileContext.pJobName is pointing to a local buffer which is initialized in initializeLocalBuffers
     * function which is again called in OTA_Init.*/
    fileContext.pJobName = &jobNameBuffer;

    /* Havoc otaAgent to non-deterministically set all the bytes in
     * the structure. */
    __CPROVER_havoc_object( &otaAgent );

    /* This assumption is used to have nondeterministic length of the jobName String. */
    __CPROVER_assume( jobNameIdx < OTA_JOB_ID_MAX_SIZE );

    otaAgent.pActiveJobName[ jobNameIdx ] = '\0';

    /* err can only assume values which are of OtaJobParseErr_t enum. */
    __CPROVER_assume( ( err >= OtaJobParseErrUnknown ) && ( err <= OtaJobParseErrNoActiveJobs ) );

    /* handleJobParsingError can never be called if the parsing err is OtaJobParseErrNone. */
    __CPROVER_assume( err != OtaJobParseErrNone );

    /* Preconditions. */
    otaAgent.OtaAppCallback = otaAppCallbackStub;
    otaControlInterface.updateJobStatus = updateJobStatusStub;

    handleJobParsingError( &fileContext, err );
}
