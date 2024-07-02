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
 * @file setDataInterface_harness.c
 * @brief Implements the proof harness for setDataInterface function.
 */
/* Ota interface includes. */
#include "ota_interface_private.h"

void setDataInterface_harness()
{
    OtaDataInterface_t * pDataInterface;
    OtaDataInterface_t dataInterface;
    OtaErr_t err;

    /* The input to the setDataInterface is a buffer statically initialized in the
     *  source code with its size defined by OTA_PROTOCOL_BUFFER_SIZE. This macro is
     *  not user configurable and thus the input does not require any constraint. */
    uint8_t pProtocol[ OTA_PROTOCOL_BUFFER_SIZE ];

    pDataInterface = &dataInterface;

    err = setDataInterface( pDataInterface, pProtocol );

    /* The function return can only be either of two values i.e OtaErrNone or
     *  OtaErrInvalidDataProtocol. */
    __CPROVER_assert( ( err == OtaErrInvalidDataProtocol ) || ( err == OtaErrNone ),
                      "The function return can be either of those values." );
}
