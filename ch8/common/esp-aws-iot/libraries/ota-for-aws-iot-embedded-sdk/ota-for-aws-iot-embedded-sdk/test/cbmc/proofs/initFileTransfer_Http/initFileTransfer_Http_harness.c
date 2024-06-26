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
 * @file initFileTransfer_Http_harness.c
 * @brief Implements the proof harness for initFileTransfer_Http function.
 */
/* Http interface includes. */
#include "ota_http_private.h"

/* Stub required for the proof. */
OtaHttpStatus_t init( char * pUrl )
{
    OtaHttpStatus_t status;

    return status;
}

void initFileTransfer_Http_harness()
{
    OtaAgentContext_t * pAgentCtx;
    OtaFileContext_t fileContext;
    OtaHttpInterface_t http;
    OtaHttpStatus_t status;
    OtaInterfaces_t interface;
    OtaAgentContext_t agent;

    pAgentCtx = &agent;

    pAgentCtx->fileContext = fileContext;

    /* The init reference in the http interface is expected to be initialized by the user and is enforced in
     * the initFileTransfer_Http function. */
    http.init = init;

    interface.http = http;
    pAgentCtx->pOtaInterface = &interface;

    status = initFileTransfer_Http( pAgentCtx );

    /* The function should either return OtaErrNone or OtaErrCleanupDataFailed. */
    __CPROVER_assert( ( status == OtaErrNone ) ||
                      ( status == OtaErrInitFileTransferFailed ),
                      "Invalid return value from initFileTransfer_Http:Expected value is either OtaErrNone or OtaErrInitFileTransferFailed." );
}
