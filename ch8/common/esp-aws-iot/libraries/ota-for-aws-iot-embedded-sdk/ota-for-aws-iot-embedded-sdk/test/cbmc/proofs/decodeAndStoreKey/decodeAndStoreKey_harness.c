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
 * @file decodeAndStoreKey_harness.c
 * @brief Implements the proof harness for decodeAndStoreKey function.
 */
/*  Ota Agent includes. */
#include "ota.h"
#include "ota_base64_private.h"

extern OtaAgentContext_t otaAgent;
extern DocParseErr_t decodeAndStoreKey( const char * pValueInJson,
                                        size_t valueLength,
                                        void * pParamAdd );

void decodeAndStoreKey_harness()
{
    DocParseErr_t parseErr;
    OtaFileContext_t * fileContext;
    const char pValueInJson[ OTA_FILE_BLOCK_SIZE ];
    size_t valueLength;
    Sig_t value;
    void * pParamAdd;

    /* Havoc otaAgent to non-deterministically set all the bytes in
     * the structure. */
    __CPROVER_havoc_object( &otaAgent );

    /* valueLength cannot exceed the size of the string buffer. */
    __CPROVER_assume( valueLength < OTA_FILE_BLOCK_SIZE );

    /* decodeAndStoreKey is called only when the value pointed in pValueInJson is of
     * Sig_t type. pParamAdd is a pointer to the pSignature in the fileContext and hence
     * cannot be NULL. */
    otaAgent.fileContext.pSignature = &value;
    pParamAdd = &( otaAgent.fileContext.pSignature );

    parseErr = decodeAndStoreKey( pValueInJson, valueLength, pParamAdd );

    __CPROVER_assert( ( parseErr >= DocParseErrUnknown ) && ( parseErr <= DocParseErrInvalidToken ),
                      "Error: Return value should be of DocParseErr_t enum. " );
}
