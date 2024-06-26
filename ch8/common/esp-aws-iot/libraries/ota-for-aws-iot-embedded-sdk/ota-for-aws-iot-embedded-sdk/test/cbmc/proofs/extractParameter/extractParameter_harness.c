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
 * @file extractParameter_harness.c
 * @brief Implements the proof harness for extractParameter function.
 */
/*  Ota Agent includes. */
#include "ota.h"
#include <stdlib.h>
#include <string.h>

extern OtaAgentContext_t otaAgent;
extern JsonDocParam_t otaJobDocModelParamStructure[ OTA_NUM_JOB_PARAMS ];

extern DocParseErr_t extractParameter( JsonDocParam_t docParam,
                                       void * pContextBase,
                                       const char * pValueInJson,
                                       size_t valueLength );

DocParseErr_t extractAndStoreArray( const char * pKey,
                                    const char * pValueInJson,
                                    size_t valueLength,
                                    void * pParamAdd,
                                    uint32_t * pParamSizeAdd )
{
    DocParseErr_t err;

    __CPROVER_assert( pParamAdd != NULL, "Error: Expected a Non-Null value for pParam." );
    __CPROVER_assert( pParamSizeAdd != NULL, "Error: Expected a Non-Null value for pParamSizeAdd." );
    __CPROVER_assert( pValueInJson != NULL, "Error: Expected a Non-Null value for pValueInJson." );

    return err;
}

DocParseErr_t decodeAndStoreKey( const char * pValueInJson,
                                 size_t valueLength,
                                 void * pParamAdd )
{
    DocParseErr_t err;

    __CPROVER_assert( pValueInJson != NULL, "Error: Expected a Non-Null value for pValueInJson." );
    __CPROVER_assert( pParamAdd != NULL, "Error: Expected a Non-Null value for pParam." );

    return err;
}

unsigned long strtoul( const char * __restrict__ __nptr,
                       char ** __restrict__ __endptr,
                       int __base )
{
    unsigned long val;

    __CPROVER_assume( val <= UINT32_MAX );

    return val;
}

void extractParameter_harness()
{
    JsonDocParam_t docParam;
    void * pContextBase;
    char * pValueInJson;
    size_t valueLength;

    OtaFileContext_t fileContext;
    size_t idx;

    /* Pre-conditions. */

    /* Havoc otaAgent to non-deterministically set all the bytes in
     * the structure. */
    __CPROVER_havoc_object( &otaAgent );

    /* The value of docParam is taken from the fields of otaJobDocModelParamStructure which is
     * enforced in parseJSONbyModel. */
    __CPROVER_assume( idx < OTA_NUM_JOB_PARAMS );
    docParam = otaJobDocModelParamStructure[ idx ];

    /* valueLength is the length of the parameter and thus cannot be NULL. */
    __CPROVER_assume( valueLength != 0 );

    /* pValueInJson is a pointer to the parameter from the json string pJson in parseJSONbyModel
     * function. */
    pValueInJson = ( char * ) malloc( sizeof( char ) * valueLength );
    __CPROVER_assume( pValueInJson != NULL );

    memset( pValueInJson, 'a', valueLength );
    pValueInJson[ valueLength - 1 ] = '\0';

    /* extractParameter is only called when the pDestOffset in the docParam is set to an offset
     * other than OTA_DONT_STORE_PARAM and OTA_STORE_NESTED_JSON. */
    __CPROVER_assume( ( docParam.pDestOffset != OTA_DONT_STORE_PARAM ) && ( docParam.pDestOffset != OTA_STORE_NESTED_JSON ) );

    /* pContextBase is a pointer to the otaAgent.fileContext which is statically initialized in ota.c */
    pContextBase = &fileContext;

    ( void ) extractParameter( docParam, pContextBase, pValueInJson, valueLength );

    free( pValueInJson );
}
