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
 * @file processValidFileContext_harness.c
 * @brief Implements the proof harness for processValidFileContext function.
 */
/*  Ota Agent includes. */
#include "ota.h"
#include "stubs.h"
#include "ota_interface_private.h"
#include <stdlib.h>

extern OtaAgentContext_t otaAgent;
extern OtaErr_t processValidFileContext( void );

void processValidFileContext_harness()
{
    OtaErr_t err;
    OtaFileContext_t fileContext;
    OtaInterfaces_t otaInterface;
    size_t size;

    fileContext.pProtocols = ( uint8_t * ) malloc( size );

    /* Initialize otaAgent. */
    otaInterface.pal.getPlatformImageState = getPlatformImageStateStub;
    otaInterface.pal.reset = resetPalStub;
    otaInterface.os.event.send = sendEventStub;

    /* Havoc otaAgent to non-deterministically set all the bytes in
     * the structure. */
    __CPROVER_havoc_object( &otaAgent );

    /* otaAgent.pOtaInterface can never be NULL as it is checked during the start of OTA Agent
     * in the receiveAndProcessOtaEvent function.*/
    otaAgent.pOtaInterface = &otaInterface;
    otaAgent.fileContext = fileContext;

    err = processValidFileContext();

    __CPROVER_assert( ( err >= OtaErrNone ) && ( err <= OtaErrActivateFailed ),
                      "Error: Return value from processValidFileContext should follow values of OtaErr_t enum." );
}
