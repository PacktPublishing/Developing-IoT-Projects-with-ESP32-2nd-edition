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
 * @file OTA_SignalEvent_harness.c
 * @brief Implements the proof harness for OTA_SignalEvent function.
 */
/* Include headers for ota agent. */
#include "ota.h"
#include "ota.c"

/* Stub for sending os events data. */
OtaOsStatus_t send( OtaEventContext_t * pEventCtx,
                    const void * pEventMsg,
                    unsigned int timeout )
{
    OtaOsStatus_t sendStatus;

    return sendStatus;
}

void OTA_SignalEvent_harness()
{
    OtaEventMsg_t eventMsg;
    OtaInterfaces_t otaInterface;

    otaInterface.os.event.send = send;
    otaAgent.pOtaInterface = &otaInterface;

    OTA_SignalEvent( &eventMsg );
}
