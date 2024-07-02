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
 * @file validateAndStartJob_harness.c
 * @brief Implements the proof harness for validateAndStartJob function.
 */
/*  Ota Agent includes. */
#include "ota.h"
#include "stubs.h"
#include "ota_interface_private.h"
#include <stdlib.h>
#include <string.h>

extern OtaAgentContext_t otaAgent;
extern OtaJobParseErr_t validateAndStartJob( OtaFileContext_t * pFileContext,
                                             OtaFileContext_t ** pFinalFile,
                                             bool * pUpdateJob );

void validateAndStartJob_harness()
{
    OtaFileContext_t fileContext; /* pFileContext can never be NULL as it is a field of statically declared otaAgent struct. */
    OtaFileContext_t * pFinalFile;
    bool updateJob;
    char jobName[ OTA_JOB_ID_MAX_SIZE ];
    size_t jobSize;
    size_t activeJobNameSize;

    /* Havoc otaAgent and fileContext to non-deterministically set all
     * the bytes in the object. */
    __CPROVER_havoc_object( &otaAgent );

    /* Non-deterministically set the sizes of the jobName strings in
     * otaAgent and fileContext. */
    __CPROVER_assume( jobSize < OTA_JOB_ID_MAX_SIZE );
    __CPROVER_assume( activeJobNameSize < OTA_JOB_ID_MAX_SIZE );

    /* The size of the activeJobName buffer should always be greater than
     * the size of new job name. */
    __CPROVER_assume( activeJobNameSize > jobSize );

    fileContext.pJobName = jobName;

    /* Non-deterministically set the terminating character of the
     * job name buffers. */
    memset( fileContext.pJobName, 'a', jobSize );
    memset( otaAgent.pActiveJobName, 'a', activeJobNameSize );

    otaAgent.pActiveJobName[ activeJobNameSize ] = '\0';
    fileContext.pJobName[ jobSize ] = '\0';

    ( void ) validateAndStartJob( &fileContext, &pFinalFile, &updateJob );
}
