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
 * @file verifyRequiredParamsExtracted_harness.c
 * @brief Implements the proof harness for verifyRequiredParamsExtracted function.
 */
/*  Ota Agent includes. */
#include "ota.h"

DocParseErr_t __CPROVER_file_local_ota_c_verifyRequiredParamsExtracted( const JsonDocParam_t * pModelParam,
                                                                        const JsonDocModel_t * pDocModel );

void verifyRequiredParamsExtracted_harness()
{
    /* docModel cannot be NULL as it is statically initialized in parseJobDoc function
     * before being passed to verifyRequiredParamsExtracted function.*/
    JsonDocModel_t docModel;
    JsonDocParam_t modelParams;
    DocParseErr_t err;

    /* Havoc docModel and modelParams to non-deterministically set all the bytes in
     * the structure. */
    __CPROVER_havoc_object( &docModel );
    __CPROVER_havoc_object( &modelParams );

    /* The number of parameters in the json document model are defined by OTA_NUM_JOB_PARAMS. */
    __CPROVER_assume( docModel.numModelParams <= OTA_NUM_JOB_PARAMS + 1 );

    err = __CPROVER_file_local_ota_c_verifyRequiredParamsExtracted( &modelParams, &docModel );

    __CPROVER_assert( ( err == DocParseErrNone ) || ( err == DocParseErrMalformedDoc ),
                      "Error: Expected return value to be either DocParseErrNone or DocParseErrMalformedDoc" );
}
