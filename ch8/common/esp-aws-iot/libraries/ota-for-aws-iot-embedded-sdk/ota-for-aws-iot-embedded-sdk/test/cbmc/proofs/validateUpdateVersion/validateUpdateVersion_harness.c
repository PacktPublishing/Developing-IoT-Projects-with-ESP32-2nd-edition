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
 * @file validateUpdateVersion_harness.c
 * @brief Implements the proof harness for validateUpdateVersion function.
 */
/*  Ota Agent includes. */
#include "ota.h"

extern OtaAgentContext_t otaAgent;
extern OtaErr_t validateUpdateVersion( const OtaFileContext_t * pFileContext );

void validateUpdateVersion_harness()
{
    /* otaAgent.fileContext is the file context which is passed to this function and can
     * be verified in parseJobDoc function. Since otaAgent is statically initialized the
     * fileContext field in it can never be NULL. */
    OtaFileContext_t fileContext;
    OtaErr_t err;

    /* CBMC preconditions.*/

    /* Havoc otaAgent and otaAgent to non-deterministically set all the bytes in
     * the object. */
    __CPROVER_havoc_object( &fileContext );
    __CPROVER_havoc_object( &otaAgent );

    err = validateUpdateVersion( &fileContext );

    __CPROVER_assert( ( err == OtaErrNone ) || ( err == OtaErrSameFirmwareVersion ) ||
                      ( err == OtaErrDowngradeNotAllowed ),
                      "Error: Expected err to be either OtaErrNone, OtaErrSameFirmwareVersion or OtaErrDowngradeNotAllowed." );
}
