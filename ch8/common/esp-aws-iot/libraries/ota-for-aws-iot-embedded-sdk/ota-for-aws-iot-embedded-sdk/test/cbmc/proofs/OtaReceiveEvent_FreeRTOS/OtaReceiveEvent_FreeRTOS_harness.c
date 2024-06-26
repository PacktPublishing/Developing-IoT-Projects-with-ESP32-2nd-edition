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
 * @file OtaReceiveEvent_FreeRTOS_harness.c
 * @brief Implements the proof harness for OtaReceiveEvent_FreeRTOS function.
 */
/*  FreeRTOS includes for OTA library. */
#include "ota_os_freertos.h"
#include "ota_private.h"
#include "FreeRTOSConfig.h"

void OtaReceiveEvent_FreeRTOS_harness()
{
    OtaEventContext_t * pEventCtx;
    OtaOsStatus_t osStatus;
    void * pEventMsg;
    uint32_t timeout;

    void * pEventMsg = ( void * ) malloc( sizeof( OtaEventMsg_t ) );

    /* pEventMsg is statically declared before it is used in this function. */
    __CPROVER_assume( pEventMsg != NULL );

    /* To avoid pdMS_TO_TICKS from integer overflow. */
    __CPROVER_assume( timeout < ( UINT32_MAX / ( configTICK_RATE_HZ ) ) );

    osStatus = OtaReceiveEvent_FreeRTOS( pEventCtx, pEventMsg, timeout );

    __CPROVER_assert( osStatus == OtaOsSuccess || osStatus == OtaOsEventQueueReceiveFailed,
                      "Invalid return value: osStatus should be either OtaOsSuccess or OtaOsEventQueueReceiveFailed." );

    free( pEventMsg );
}
