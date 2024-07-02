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
 * @file validateDataBlock_harness.c
 * @brief Implements the proof harness for validateDataBlock function.
 */
/*  Ota Agent includes. */
#include "ota.h"

bool __CPROVER_file_local_ota_c_validateDataBlock( const OtaFileContext_t * pFileContext,
                                                   uint32_t blockIndex,
                                                   uint32_t blockSize );

void validateDataBlock_harness()
{
    OtaFileContext_t fileContext;
    uint32_t blockIndex;
    uint32_t blockSize;

    /* Havoc fileContext to non-deterministically set all the bytes in
     * the structure. */
    __CPROVER_havoc_object( &fileContext );

    /* The minimum and maximum size of the fileSize is (0, MAX_FILE_SIZE). MAX_FILE_SIZE is defined
     * in the Makefile of this proof. */
    __CPROVER_assume( ( fileContext.fileSize > 0 ) && ( fileContext.fileSize <= MAX_FILE_SIZE ) );

    ( void ) __CPROVER_file_local_ota_c_validateDataBlock( &fileContext, blockIndex, blockSize );
}
