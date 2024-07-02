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
 * @file initDocModel_harness.c
 * @brief Implements the proof harness for initDocModel function.
 */
/*  Ota Agent includes. */
#include "ota.h"
#include <stdlib.h>

DocParseErr_t __CPROVER_file_local_ota_c_initDocModel( JsonDocModel_t * pDocModel,
                                                       const JsonDocParam_t * pBodyDef,
                                                       void * contextBaseAddr,
                                                       uint32_t contextSize,
                                                       uint16_t numJobParams );

void initDocModel_harness()
{
    DocParseErr_t err;
    JsonDocModel_t * pDocModel;
    JsonDocParam_t * pBodyDef;
    void * contextBaseAddr;
    uint32_t contextSize;
    uint16_t numJobParams;

    pDocModel = ( JsonDocModel_t * ) malloc( sizeof( JsonDocModel_t ) );

    /* The number of parameters in pBodyDef is defined by the numJobParams. */
    pBodyDef = ( JsonDocParam_t * ) malloc( sizeof( JsonDocParam_t ) * numJobParams );

    err = __CPROVER_file_local_ota_c_initDocModel( pDocModel, pBodyDef, contextBaseAddr, contextSize, numJobParams );

    __CPROVER_assert( ( err >= DocParseErrUnknown ) && ( err <= DocParseErrInvalidToken ),
                      "Invalid return val: Expected err to have values from DocParseErr_t enum." );
    free( pDocModel );
    free( pBodyDef );
}
