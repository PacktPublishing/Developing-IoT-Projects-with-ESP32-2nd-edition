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
 * @file platformInSelftest_harness.c
 * @brief Implements the proof harness for platformInSelftest function.
 */
/*  Ota Agent includes. */
#include "ota.h"
#include "stubs.h"

extern OtaAgentContext_t otaAgent;
extern bool platformInSelftest( void );

void platformInSelftest_harness()
{
    OtaInterfaces_t otaInterface;
    bool state;

    /* Havoc otaAgent to non-deterministically set all the bytes in
     * the structure. */
    __CPROVER_havoc_object( &otaAgent );

    otaInterface.pal.getPlatformImageState = getPlatformImageStateStub;

    /* At the start of the Agent, otaAgent.pOtaInterface is always checked to be
     * non-NULL in the receiveAndProcessOtaEvent function. */
    otaAgent.pOtaInterface = &otaInterface;

    state = platformInSelftest();

    __CPROVER_assert( ( state == true ) || ( state == false ),
                      "Error: Expected value should be a bool value. " );
}
