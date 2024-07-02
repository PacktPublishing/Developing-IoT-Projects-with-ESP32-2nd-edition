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
 * @file OTA_Shutdown_harness.c
 * @brief Implements the proof harness for OTA_Shutdown function.
 */
/*  Ota Agent includes. */
#include "ota.h"
#include "stubs.h"

extern OtaAgentContext_t otaAgent;

void OTA_Shutdown_harness()
{
    OtaState_t state;
    uint32_t ticksToWait;
    uint8_t unsubscribeFlag;
    OtaInterfaces_t otaInterface;

    otaAgent.state = state;

    /* This assumption is required to have an upper bound on the unwinding of while loop in
     * OTA_Shutdown. This does not model the exact behavior of the code since the limitation of CBMC
     * is that it checks concurrent code in sequential manner.*/
    __CPROVER_assume( ticksToWait < 3 );

    /* otaAgent.state must only have values of OtaState_t enum type. */
    __CPROVER_assume( ( otaAgent.state >= OtaAgentStateNoTransition ) && ( otaAgent.state <= OtaAgentStateAll ) );

    state = OTA_Shutdown( ticksToWait, unsubscribeFlag );

    /* OTA_Shutdown returns the values which follow OtaState_t enum. If it does, then
     * there is a problem. */
    __CPROVER_assert( ( state >= OtaAgentStateNoTransition ) && ( otaAgent.state <= OtaAgentStateAll ),
                      "Invalid return value from OTA_Shutdown: Expected a value from OtaState_t enum." );
}
