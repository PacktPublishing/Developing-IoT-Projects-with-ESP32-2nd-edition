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
 * @file decodeBase64IndexBuffer_harness.c
 * @brief Implements the proof harness for decodeBase64IndexBuffer function.
 */
/* Include headers for base64 decoding. */
#include "ota_base64_private.h"

/* Only 24bits are required to store the 4 sextets of the encoded value. */
#define MAX_BITS_IN_DECODE_BUFFER      24U

/* Smallest amount of data that can be Base64 encoded is a byte. */
#define MIN_VALID_ENCODED_DATA_SIZE    2U

/* Maximum number of Base64 symbols to store in a buffer before decoding them. */
#define MAX_NUM_BASE64_DATA            4U

/* Declaration of the mangled name static function which is created by CBMC for static functions. */
Base64Status_t __CPROVER_file_local_ota_base64_c_decodeBase64IndexBuffer( uint8_t * pDest,
                                                                          const size_t destLen,
                                                                          size_t * pResultLen,
                                                                          const uint8_t * pEncodedData,
                                                                          const size_t encodedLen );

void decodeBase64IndexBuffer_harness()
{
    uint32_t * pBase64IndexBuffer;
    uint32_t * pNumDataInBuffer;
    uint8_t * pDest;
    size_t destLen;
    size_t * pOutputLen;
    uint32_t base64IndexBuffer;
    uint32_t numDataInBuffer;
    size_t outputLen;

    /* These values are defined in the base64Decode function before passing
     * it to the decodeBase64IndexBuffer function and thus cannot be NULL. */
    pBase64IndexBuffer = &base64IndexBuffer;
    pNumDataInBuffer = &numDataInBuffer;
    pOutputLen = &outputLen;

    /* The outputLen is the length of the decoded data filled in the
     * pDest buffer. This value cannot exceed UINT32_MAX - 4. */
    __CPROVER_assume( outputLen < UINT32_MAX - 4 );

    pDest = ( uint8_t * ) malloc( destLen * sizeof( uint8_t ) );

    /* This condition is used to prevent scenarios where malloc fails and
     * returns NULL pointer. */
    __CPROVER_assume( pDest != NULL );

    /* The pNumDataInBuffer stores the number of bytes present in the base64Buffer.
     * The minimum and maximum number of bytes stored in the buffer are defined. */
    __CPROVER_assume( *pNumDataInBuffer >= MIN_VALID_ENCODED_DATA_SIZE && *pNumDataInBuffer <= MAX_NUM_BASE64_DATA );

    ( void ) __CPROVER_file_local_ota_base64_c_decodeBase64IndexBuffer( pBase64IndexBuffer, pNumDataInBuffer, pDest, destLen, pOutputLen );

    free( pDest );
}
