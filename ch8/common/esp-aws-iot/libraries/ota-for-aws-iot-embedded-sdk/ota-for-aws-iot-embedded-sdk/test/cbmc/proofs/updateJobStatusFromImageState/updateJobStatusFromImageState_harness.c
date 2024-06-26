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
 * @file updateJobStatusFromImageState_harness.c
 * @brief Implements the proof harness for updateJobStatusFromImageState function.
 */
/*  Ota Agent includes. */
#include "ota.h"
#include "ota_interface_private.h"
#include "stubs.h"

extern OtaControlInterface_t otaControlInterface;
extern OtaErr_t updateJobStatusFromImageState( OtaImageState_t state,
                                               int32_t subReason );

void updateJobStatusFromImageState_harness()
{
    OtaImageState_t state;
    int32_t subReason;
    OtaErr_t err;

    __CPROVER_assume( ( state >= OtaImageStateUnknown ) && ( state <= OtaImageStateAborted ) );

    /* CBMC pre-conditions. */

    /* Havoc otaControlInterface to non-deterministically set all
     * the bytes in the object. */
    __CPROVER_havoc_object( &otaControlInterface );

    otaControlInterface.updateJobStatus = updateJobStatusStub;

    err = updateJobStatusFromImageState( state, subReason );

    /* updateJobStatusFromImageState returns the values which follow OtaErr_t enum. If it does, then
     * there is a problem. */
    __CPROVER_assert( ( err >= OtaErrNone ) && ( err <= OtaErrActivateFailed ),
                      "Invalid return value from updateJobStatusFromImageState: Expected value of OtaErr_t enum." );
}
