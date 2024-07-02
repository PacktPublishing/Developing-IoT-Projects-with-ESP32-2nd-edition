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
 * @file agentShutdownCleanup_harness.c
 * @brief Implements the proof harness for agentShutdownCleanup function.
 */
/*  Ota Agent includes. */
#include "ota.h"
#include "ota_interface_private.h"
#include "stubs.h"

/* Global static variable defined in ota.c for managing the state machine. */
extern OtaControlInterface_t otaControlInterface;
extern OtaDataInterface_t otaDataInterface;
extern OtaAgentContext_t otaAgent;
extern void agentShutdownCleanup( void );

void agentShutdownCleanup_harness()
{
    OtaInterfaces_t otaInterface;

    /* Initialize os timers functions. */
    otaInterface.os.timer.stop = stopTimerStub;
    otaInterface.os.timer.delete = deleteTimerStub;

    otaAgent.pOtaInterface = &otaInterface;

    /* Initialize the function pointers to stubs. */
    otaControlInterface.cleanup = cleanupStub;
    otaDataInterface.cleanup = cleanupStub;

    agentShutdownCleanup();
}
