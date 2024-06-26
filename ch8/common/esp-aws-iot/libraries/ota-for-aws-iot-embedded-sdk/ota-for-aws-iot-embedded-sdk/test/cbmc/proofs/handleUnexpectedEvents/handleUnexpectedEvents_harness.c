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
 * @file handleUnexpectedEvents_harness.c
 * @brief Implements the proof harness for handleUnexpectedEvents function.
 */
/*  Ota Agent includes. */
#include "ota.h"
#include "stubs.h"
#include <stdlib.h>

extern OtaAgentContext_t otaAgent;
extern void handleUnexpectedEvents( const OtaEventMsg_t * pEventMsg );

void handleUnexpectedEvents_harness()
{
    /* eventMsg cannot be NULL as it is statically initialized in receiveAndProcessOtaEvent
     * before handleUnexpectedEvents function is called. */
    OtaEventMsg_t eventMsg;

    /* Havoc otaAgent and eventMsg to non-deterministically set all the bytes in
     * the structure. */
    __CPROVER_havoc_object( &eventMsg );
    __CPROVER_havoc_object( &otaAgent );

    /* Initialize OtaAppCallback to an empty callback function. */
    otaAgent.OtaAppCallback = otaAppCallbackStub;

    /* The maximum number of packets/blocks dropped by the otaAgent should be
     * less than the file size. This assumption is valid even for file with sizes
     * from (0, UINT32_MAX). */
    __CPROVER_assume( otaAgent.statistics.otaPacketsDropped < UINT32_MAX );

    handleUnexpectedEvents( &eventMsg );
}
