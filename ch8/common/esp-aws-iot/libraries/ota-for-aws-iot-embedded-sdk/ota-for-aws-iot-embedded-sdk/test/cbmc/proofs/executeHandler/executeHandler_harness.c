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
 * @file executeHandler_harness.c
 * @brief Implements the proof harness for executeHandler function.
 */
/*  Ota Agent includes. */
#include "ota.h"

void __CPROVER_file_local_ota_c_executeHandler( uint32_t index,
                                                const OtaEventMsg_t * const pEventMsg );

void executeHandler_harness()
{
    uint32_t index;
    OtaEventMsg_t * pEventMsg;

    pEventMsg = ( OtaEventMsg_t * ) malloc( sizeof( OtaEventMsg_t ) );

    /* pEventMsg is statically defined in receiveAndProcessOtaEvent before the call to
     * executeHandler. */
    __CPROVER_assume( pEventMsg != NULL );

    /* otaTransitionTable have indexes ranging from [0,18]. */
    __CPROVER_assume( ( index >= 0 ) && ( index <= 18 ) );

    __CPROVER_file_local_ota_c_executeHandler( index, pEventMsg );

    free( pEventMsg );
}
