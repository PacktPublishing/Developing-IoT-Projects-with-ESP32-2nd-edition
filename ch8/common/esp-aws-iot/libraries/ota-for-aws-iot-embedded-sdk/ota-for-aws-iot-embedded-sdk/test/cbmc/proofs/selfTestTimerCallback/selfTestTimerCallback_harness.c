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
 * @file selfTestTimerCallback_harness.c
 * @brief Implements the proof harness for selfTestTimerCallback function.
 */
/*  FreeRTOS includes for OTA library. */
#include "ota_os_freertos.h"
#include "FreeRTOS.h"
#include "timers.h"

/* Declaration of the mangled name function created by CBMC for static functions.*/
void __CPROVER_file_local_ota_os_freertos_c_selfTestTimerCallback( TimerHandle_t timer );

void otaTimerCallback( OtaTimerId_t otaTimerId )
{
    __CPROVER_assert( ( otaTimerId == OtaRequestTimer ) || ( otaTimerId == OtaSelfTestTimer ),
                      "Invalid OtaTimerId: Expected OtaRequestTimer" );
}

void selfTestTimerCallback_harness()
{
    TimerHandle_t timer;
    OtaTimerId_t otaTimerId;
    const char * pTimerName;
    size_t thingNameSize;
    uint32_t timeout;

    pTimerName = ( const char * ) malloc( thingNameSize * sizeof( char ) );

    /* OtaStartTimer functions requires the pTimerName and otaCallback not
     * to be NULL. */
    __CPROVER_assume( pTimerName != NULL );

    /* otaTimerId can only have values of OtaTimerId_t enumeration. */
    __CPROVER_assume( otaTimerId == OtaRequestTimer || otaTimerId == OtaSelfTestTimer );

    /* To avoid integer overflow in pdMs_TO_TICKS. */
    __CPROVER_assume( timeout < ( UINT32_MAX / configTICK_RATE_HZ ) );

    /* OtaStartTimer_FreeRTOS initializes the function pointer OtaTimerCallback. */
    OtaStartTimer_FreeRTOS( otaTimerId,
                            pTimerName,
                            timeout,
                            otaTimerCallback );

    __CPROVER_file_local_ota_os_freertos_c_selfTestTimerCallback( timer );

    free( pTimerName );
}
