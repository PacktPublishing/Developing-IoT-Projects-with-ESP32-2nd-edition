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
 * @file otaTimerCallback_harness.c
 * @brief Implements the proof harness for otaTimerCallback function.
 */
/*  Ota Agent includes. */
#include "ota.h"
#include "stubs.h"

extern OtaAgentContext_t otaAgent;
extern void otaTimerCallback( OtaTimerId_t otaTimerId );

void otaTimerCallback_harness()
{
    OtaTimerId_t otaTimerId;
    OtaInterfaces_t otaInterface;

    /* Havoc otaAgent to non-deterministically set all the bytes in
     * the structure. */
    __CPROVER_havoc_object( &otaAgent );

    /* otaTimerId can only assume value of OtaTimerId_t enum. */
    __CPROVER_assume( ( otaTimerId == OtaRequestTimer ) || ( otaTimerId == OtaSelfTestTimer ) );

    /* CBMC preconditions. */
    otaInterface.pal.reset = resetPalStub;
    otaInterface.os.event.send = sendEventStub;

    /* otaAgent.pOtaInterface can never be NULL as it is always checked at the start of the OTA
     * Agent specifically in receiveAndProcessOTAEvent function.*/
    otaAgent.pOtaInterface = &otaInterface;

    otaTimerCallback( otaTimerId );
}
