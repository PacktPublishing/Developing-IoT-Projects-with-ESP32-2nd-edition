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
 * @file initializeLocalBuffers_harness.c
 * @brief Implements the proof harness for initializeLocalBuffers function.
 */
/*  Ota Agent includes. */
#include "ota.h"

extern OtaAgentContext_t otaAgent;
extern void initializeLocalBuffers( void );

void initializeLocalBuffers_harness()
{
    /* Havoc otaAgent to non-deterministically set the bytes in the object. */
    __CPROVER_havoc_object( &otaAgent );

    initializeLocalBuffers();

    /* CBMC post-conditions. */
    __CPROVER_assert( otaAgent.fileContext.pJobName != NULL,
                      "Error: Expected initializeLocalBuffers to initialize otaAgent.fileContext.pJobName to a non-NULL value." );

    __CPROVER_assert( otaAgent.fileContext.pProtocols != NULL,
                      "Error: Expected initializeLocalBuffers to initialize otaAgent.fileContext.pProtocols to a non-NULL value." );

    __CPROVER_assert( otaAgent.fileContext.pSignature != NULL,
                      "Error: Expected initializeLocalBuffers to initialize otaAgent.fileContext.pSignature to a non-NULL value." );

    __CPROVER_assert( otaAgent.fileContext.jobNameMaxSize == OTA_JOB_ID_MAX_SIZE,
                      "Error: Expected initializeLocalBuffers to set the otaAgent.fileCOntext.jobNameMaxSize field to OTA_JOB_ID_MAX_SIZE " );

    __CPROVER_assert( otaAgent.fileContext.protocolMaxSize == OTA_PROTOCOL_BUFFER_SIZE,
                      "Error: Expected initializeLocalBuffers to set the otaAgent.fileCOntext.protocolMaxSize field to OTA_PROTOCOL_BUFFER_SIZE " );
}
