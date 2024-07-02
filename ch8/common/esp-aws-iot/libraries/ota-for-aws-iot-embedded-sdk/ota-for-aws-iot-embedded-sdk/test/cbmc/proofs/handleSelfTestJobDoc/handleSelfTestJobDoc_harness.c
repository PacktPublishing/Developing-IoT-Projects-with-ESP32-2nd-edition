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
 * @file handleSelfTestJobDoc_harness.c
 * @brief Implements the proof harness for handleSelfTestJobDoc function.
 */
/*  Ota Agent includes. */
#include "ota.h"
#include "stubs.h"

extern OtaAgentContext_t otaAgent;
extern void handleSelfTestJobDoc( const OtaFileContext_t * pFileContext );

OtaErr_t validateUpdateVersion( const OtaFileContext_t * pFileContext )
{
    OtaErr_t err;

    /* pFileContext is statically defined in parseJobDoc before validateUpdateVersion
     * is called. Hence, it cannot be NULL. */
    __CPROVER_assert( pFileContext != NULL, "Error: Expected pFileContext to be Non-NULL" );

    /* err can assume values of OtaErr_t enum. */
    __CPROVER_assume( ( err >= OtaErrNone ) && ( err <= OtaErrActivateFailed ) );

    return err;
}

void handleSelfTestJobDoc_harness()
{
    OtaFileContext_t fileContext;
    OtaInterfaces_t otaInterface;

    /* To set all the fields in otaAgent to non-deterministic values. */
    __CPROVER_havoc_object( &otaAgent );

    otaInterface.pal.reset = resetPalStub;
    otaAgent.OtaAppCallback = otaAppCallbackStub;

    /* Initialize otaAgent. */
    otaAgent.pOtaInterface = &otaInterface;
    otaAgent.fileContext = fileContext;

    handleSelfTestJobDoc( &( otaAgent.fileContext ) );
}
