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
 * @file OTA_Suspend_harness.c
 * @brief Implements the proof harness for OTA_Suspend function.
 */
/*  Ota Agent includes. */
#include "ota.h"

extern OtaAgentContext_t otaAgent;

/* Stub for stop function in os.timer interface. */
OtaOsStatus_t timerStop( OtaTimerId_t otaTimerId )
{
    OtaOsStatus_t status;

    /* otaTimerId must only have values of OtaTimerId_t enum. */
    __CPROVER_assert( ( otaTimerId == OtaRequestTimer ) || ( otaTimerId == OtaSelfTestTimer ),
                      "Error: otaTimerId can only have values OtaRequestTimer or OtaSelfTestTimer." );

    /* Status must only have values of OtaOsStatus_t enum. */
    __CPROVER_assume( ( status >= OtaOsSuccess ) && ( status <= OtaOsTimerDeleteFailed ) );

    return status;
}

void OTA_Suspend_harness()
{
    OtaState_t state;
    OtaErr_t err;
    OtaInterfaces_t otaInterface;

    otaInterface.os.timer.stop = timerStop;

    /* otaAgent.pOtaInterface can never be NULL as it is always checked at the start of the OTA
     * Agent specifically in receiveAndProcessOTAEvent function.*/
    otaAgent.pOtaInterface = &otaInterface;

    /* otaAgent.state must always have values of OtaState_t enum type. */
    otaAgent.state = state;
    __CPROVER_assume( ( otaAgent.state >= OtaAgentStateNoTransition ) && ( otaAgent.state <= OtaAgentStateAll ) );

    err = OTA_Suspend();

    __CPROVER_assert( ( err == OtaErrNone ) || ( err == OtaErrAgentStopped ) ||
                      ( err == OtaErrSignalEventFailed ), "Invalid return value from OTA_Suspend: Expected OtaErrNone, OtaErrAgentStopped or OtaErrSignalEventFailed." );
}
