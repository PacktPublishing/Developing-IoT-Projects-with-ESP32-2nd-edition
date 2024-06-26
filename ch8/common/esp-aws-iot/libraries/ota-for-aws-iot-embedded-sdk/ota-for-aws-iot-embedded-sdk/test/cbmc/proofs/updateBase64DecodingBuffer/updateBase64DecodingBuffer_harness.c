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
 * @file updateBase64DecodingBuffer_harness.c
 * @brief Implements the proof harness for updateBase64DecodingBuffer function.
 */
/* Include headers for base64 decoding. */
#include "ota_base64_private.h"

/* Inclusive upper bound for valid values that can be contained in pBase64SymbolToIndexMap. */
#define SYMBOL_TO_INDEX_MAP_VALUE_UPPER_BOUND    67U

void __CPROVER_file_local_ota_base64_c_updateBase64DecodingBuffer( const uint8_t base64Index,
                                                                   uint32_t * pBase64IndexBuffer,
                                                                   uint32_t * pNumDataInBuffer );

void updateBase64DecodingBuffer_harness()
{
    uint8_t base64Index;
    uint32_t * pBase64IndexBuffer;
    uint32_t * pNumDataInBuffer;
    uint32_t base64IndexBuffer;
    uint32_t numDataInBuffer;

    pBase64IndexBuffer = &base64IndexBuffer;
    pNumDataInBuffer = &numDataInBuffer;

    /* SYMBOL_TO_INDEX_MAP_VALUE_UPPER_BOUND is the maximum value of the
     * base64Index which is enforced in ota_base64.c. */
    __CPROVER_assume( base64Index < SYMBOL_TO_INDEX_MAP_VALUE_UPPER_BOUND );

    /* The maximum number of data in the pBase64IndexBuffer should not
     * exceed UINT32_MAX. */
    __CPROVER_assume( numDataInBuffer < UINT32_MAX );

    __CPROVER_file_local_ota_base64_c_updateBase64DecodingBuffer( base64Index, pBase64IndexBuffer, pNumDataInBuffer );
}
