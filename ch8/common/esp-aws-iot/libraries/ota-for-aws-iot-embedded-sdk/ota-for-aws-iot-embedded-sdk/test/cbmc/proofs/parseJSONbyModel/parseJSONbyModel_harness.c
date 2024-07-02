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
 * @file parseJSONbyModel_harness.c
 * @brief Implements the proof harness for parseJSONbyModel function.
 */
/*  Ota Agent includes. */
#include "ota.h"
#include "core_json.h"

extern OtaAgentContext_t otaAgent;
extern JsonDocParam_t otaJobDocModelParamStructure[ OTA_NUM_JOB_PARAMS ];
extern DocParseErr_t parseJSONbyModel( const char * pJson,
                                       uint32_t messageLength,
                                       JsonDocModel_t * pDocModel );

/* Initialize the src key for JSON files. */
const char OTA_JsonFileSignatureKey[ OTA_FILE_SIG_KEY_STR_MAX_LENGTH ] = "sig-sha256-ecdsa";

/* Stub to validate the JSON string. */
DocParseErr_t validateJSON( const char * pJson,
                            uint32_t messageLength )
{
    DocParseErr_t parseErr;

    __CPROVER_assume( ( parseErr >= DocParseErrUnknown ) && ( parseErr <= DocParseErrInvalidToken ) );

    return parseErr;
}

/* Stub to search for constants in a JSON string. */
JSONStatus_t JSON_SearchConst( const char * buf,
                               size_t max,
                               const char * query,
                               size_t queryLength,
                               const char ** outValue,
                               size_t * outValueLength,
                               JSONTypes_t * outType )
{
    JSONStatus_t status;
    size_t value;

    /* valueLength cannot exceed the length of buffer.*/
    __CPROVER_assume( value > 2u && value < OTA_FILE_BLOCK_SIZE );

    *outValueLength = value;
    *outValue = buf;

    return status;
}

/* Stub to extract parameters from a JSON string. */
DocParseErr_t extractParameter( JsonDocParam_t docParam,
                                void * pContextBase,
                                const char * pValueInJson,
                                size_t valueLength )
{
    DocParseErr_t parseErr;

    /* pContextBase and pValueInJson are defined in parseJSONbyModel function
     * before calling extractParameter.*/
    __CPROVER_assert( pContextBase != NULL, "Error: Expected a non-NULL pContextBase value. " );
    __CPROVER_assert( pValueInJson != NULL, "Error: Expected a non-NULL pValueInJson value. " );

    return parseErr;
}

/* Stub to Check if all the required parameters for job document are extracted from the JSON. */
DocParseErr_t verifyRequiredParamsExtracted( const JsonDocParam_t * pModelParam,
                                             const JsonDocModel_t * pDocModel )
{
    DocParseErr_t parseErr;

    /* pModelParam and pDocModel are defined in parseJSONbyModel function
     * before calling extractParameter.*/
    __CPROVER_assert( pModelParam != NULL, "Error: Expected a non-NULL pContextBase value. " );
    __CPROVER_assert( pDocModel != NULL, "Error: Expected a non-NULL pValueInJson value. " );

    return parseErr;
}

void parseJSONbyModel_harness()
{
    /* pJson is always passed as a global buffer from OtaEventData_t which is
     * enforced in processJobHandler. */
    JsonDocModel_t docModel;
    JsonDocParam_t * modelParams;
    char pJson[ OTA_DATA_BLOCK_SIZE ];
    uint32_t messageLength;
    size_t numParams;
    size_t idx;

    /* Preconditions. */
    __CPROVER_assume( numParams < OTA_NUM_PARAMS );

    /* Havoc otaAgent to non-deterministically set all the bytes in
     * the structure. */
    __CPROVER_havoc_object( &otaAgent );

    /* Length of the message cannot exceed the size of the message buffer. */
    __CPROVER_assume( messageLength < OTA_DATA_BLOCK_SIZE );

    /* Initialize the array of document model body functions. This is always initialized
     * before passing to parseJSONbyModel function and hence cannot be NULL. */
    modelParams = ( JsonDocParam_t * ) malloc( sizeof( JsonDocParam_t ) * numParams );
    __CPROVER_assume( modelParams != NULL );

    /* Havoc object to non-deterministically set all the bytes in the
     * object. */
    __CPROVER_havoc_object( modelParams );

    /* Initialize modelParams.pSrcKey string of non-deterministic length. */
    for( idx = 0; idx < numParams; ++idx )
    {
        size_t size;
        char * pStr;

        /* Non-deterministically set the size of the pSrcKey. */
        __CPROVER_assume( size > 0u && size < OTA_JSON_SRC_KEY_SIZE );

        pStr = ( char * ) malloc( sizeof( char ) * size );
        __CPROVER_assume( pStr != NULL );

        pStr[ size - 1 ] = '\0';

        modelParams[ idx ].pSrcKey = pStr;
    }

    /* Initialize the docModel. */
    docModel.pBodyDef = modelParams;
    docModel.numModelParams = numParams;
    docModel.contextBase = &( otaAgent.fileContext );
    docModel.contextSize = sizeof( OtaFileContext_t );

    ( void ) parseJSONbyModel( pJson, messageLength, &docModel );

    for( idx = 0; idx < numParams; ++idx )
    {
        free( modelParams[ idx ].pSrcKey );
    }

    free( modelParams );
}
