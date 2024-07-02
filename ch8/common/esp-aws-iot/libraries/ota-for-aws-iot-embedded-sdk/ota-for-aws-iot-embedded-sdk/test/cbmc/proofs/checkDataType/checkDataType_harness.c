/*
 * AWS IoT Over-the-air Update v3.4.0
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * @file checkDataType_harness.c
 * @brief Implements the proof harness for checkDataType function.
 */
/* Include headers for cbor parsing. */
#include "cbor.h"
#include "ota_cbor_private.h"

CborError __CPROVER_file_local_ota_cbor_c_checkDataType( CborType expectedType,
                                                         CborValue * cborValue );


void checkDataType_harness()
{
    CborType expectedType;
    CborValue cborvalue;
    CborError cborResult;

    cborResult = __CPROVER_file_local_ota_cbor_c_checkDataType( expectedType, &cborvalue );

    __CPROVER_assert( cborResult == CborNoError || cborResult == CborErrorIllegalType,
                      "Invalid cborResult value: Expected either CborNoError or CborErrorIllegalType." );
}
