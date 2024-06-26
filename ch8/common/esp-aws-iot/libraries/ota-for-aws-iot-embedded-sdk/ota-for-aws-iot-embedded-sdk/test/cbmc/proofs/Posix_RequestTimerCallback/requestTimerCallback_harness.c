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
 * @file requestTimerCallback_harness.c
 * @brief Implements the proof harness for requestTimerCallback function.
 */
/*  POSIX includes for OTA library. */
#include "ota_os_posix.h"
#include <signal.h>
#include <stdlib.h>

/* Declaration of requestTimerCallback function with a mangled name. */
void __CPROVER_file_local_ota_os_posix_c_requestTimerCallback( union sigval arg );

/* Stub for Timer callback. */
void OtaCallback( OtaTimerId_t otaTimerid )
{
}

void requestTimerCallback_harness()
{
    OtaTimerId_t otaTimerId;
    const char * pTimerName;
    size_t size;
    uint32_t timeout;
    OtaTimerCallback_t callback;
    union sigval arg;

    /* The valid range of values for OtaTimerId_t are [0,2).*/
    __CPROVER_assume( otaTimerId >= 0 && otaTimerId < 2 );

    pTimerName = ( const char * ) malloc( size * sizeof( char ) );

    /* Initializing a timer callback function. */
    callback = OtaCallback;

    /* Map the callback function in ota_posix.c to OtaCallback. */
    Posix_OtaStartTimer( otaTimerId, pTimerName, timeout, callback );

    __CPROVER_file_local_ota_os_posix_c_requestTimerCallback( arg );

    free( pTimerName );
}
