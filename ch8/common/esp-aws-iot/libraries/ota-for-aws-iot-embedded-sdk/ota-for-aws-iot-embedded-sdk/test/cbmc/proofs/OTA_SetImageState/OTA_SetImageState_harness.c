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
 * @file OTA_SetImageState_harness.c
 * @brief Implements the proof harness for OTA_SetImageState function.
 */
/*  Ota Agent includes. */
#include "ota.h"

OtaErr_t __CPROVER_file_local_ota_c_setImageStateWithReason( OtaImageState_t stateToSet,
                                                             uint32_t reasonToSet )
{
    OtaErr_t err;

    /* err will only have values of OtaErr_t enum type. */
    __CPROVER_assume( ( err >= OtaErrNone ) && ( err <= OtaErrActivateFailed ) );

    return err;
}

void OTA_SetImageState_harness()
{
    OtaImageState_t state;
    OtaErr_t status;

    /* State will only have value of OtaImageState_t enum type. */
    __CPROVER_assume( ( state >= OtaImageStateUnknown ) && ( state <= OtaImageStateAborted ) );

    status = OTA_SetImageState( state );

    __CPROVER_assert( ( status >= OtaErrNone ) && ( status <= OtaErrActivateFailed ),
                      "Invalid value for state:state follows value of OtaErr_t enum type." );
}
