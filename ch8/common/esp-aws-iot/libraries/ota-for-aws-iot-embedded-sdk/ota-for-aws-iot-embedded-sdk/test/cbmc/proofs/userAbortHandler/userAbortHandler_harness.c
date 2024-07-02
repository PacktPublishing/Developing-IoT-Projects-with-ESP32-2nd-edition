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
 * @file userAbortHandler_harness.c
 * @brief Implements the proof harness for userAbortHandler function.
 */
/*  Ota Agent includes. */
#include "ota.h"
#include <stdlib.h>
#include <string.h>

extern OtaAgentContext_t otaAgent;
extern OtaErr_t userAbortHandler( const OtaEventData_t * pEventData );

/* Stub to set the state of Image. */
OtaErr_t setImageStateWithReason( OtaImageState_t stateToSet,
                                  uint32_t reasonToSet )
{
    OtaErr_t err;

    __CPROVER_assume( ( err >= OtaErrNone ) && ( err <= OtaErrActivateFailed ) );

    return err;
}

void userAbortHandler_harness()
{
    OtaEventData_t * pEventData;
    OtaErr_t err;
    size_t size;

    /* Upper Bound on the size of the pActiveJobName string. */
    __CPROVER_assume( size < OTA_JOB_ID_MAX_SIZE );

    /* This statement is used to avoid CBMC setting any characters
     * in the string to NULL. */
    memset( otaAgent.pActiveJobName, '-', size );

    /* This ensures a Non-deterministic way of setting the size of
     * the string pActiveJobName. */
    otaAgent.pActiveJobName[ size ] = '\0';

    pEventData = ( OtaEventData_t * ) malloc( sizeof( OtaEventData_t ) );

    err = userAbortHandler( pEventData );

    /* userAbortHandler returns the values which follow OtaImageState_t enum. If it does, then
     * there is a problem. */
    __CPROVER_assert( ( err >= OtaErrNone ) && ( err <= OtaErrActivateFailed ),
                      "Invalid return value from userAbortHandler: Expected a value from OtaErr_t enum." );

    free( pEventData );
}
