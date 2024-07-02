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
 * @file OtaStartTimer_FreeRTOS_harness.c
 * @brief Implements the proof harness for OtaStartTimer_FreeRTOS function.
 */
/*  FreeRTOS includes for OTA library. */
#include "ota_os_freertos.h"
#include "FreeRTOSConfig.h"

void otaCallback( OtaTimerId_t otaTimerId )
{
    __CPROVER_assert( otaTimerId == OtaRequestTimer || otaTimerId == OtaSelfTestTimer,
                      "Invalid otaTimerId: otaTimerId should have values of OtaTimerId_t enum." );
}

void OtaStartTimer_FreeRTOS_harness()
{
    OtaTimerId_t otaTimerId;
    char * pTimerName;
    uint32_t timeout;
    OtaTimerCallback_t callback = otaCallback;
    OtaOsStatus_t osStatus;

    size_t size;

    pTimerName = ( char * ) malloc( size * sizeof( char ) );

    /* pTimerName is always initialized to OtaRequestTimer or OtaSelfTestTimer
     * before passing it to OtaStartTimer_FreeRTOS function. */
    __CPROVER_assume( pTimerName != NULL );

    /* callback is statically defined in ota.c before passing it to
     * OtaStartTiemr_FreeRTOS. */
    __CPROVER_assume( callback != NULL );

    /* To avoid pdMS_TO_TICKS from integer overflow. */
    __CPROVER_assume( timeout < ( UINT32_MAX / ( configTICK_RATE_HZ ) ) );

    /* otaTimerId can only have values of OtaTimerId_t enumeration. */
    __CPROVER_assume( otaTimerId == OtaRequestTimer || otaTimerId == OtaSelfTestTimer );

    osStatus = OtaStartTimer_FreeRTOS( otaTimerId, pTimerName, timeout, callback );

    __CPROVER_assert( osStatus == OtaOsSuccess || osStatus == OtaOsTimerCreateFailed ||
                      osStatus == OtaOsTimerStartFailed || osStatus == OtaOsTimerRestartFailed,
                      "Invalid return value for osStatus." );

    free( pTimerName );
}
