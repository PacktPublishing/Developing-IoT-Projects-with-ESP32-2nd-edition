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
 * @file extractAndStoreArray_harness.c
 * @brief Implements the proof harness for extractAndStoreArray function.
 */
/*  Ota Agent includes. */
#include "ota.h"
#include "stubs.h"
#include <stdlib.h>

extern OtaAgentContext_t otaAgent;
extern uint32_t extractAndStoreArray( const char * pKey,
                                      const char * pValueInJson,
                                      size_t valueLength,
                                      void * pParamAdd,
                                      uint32_t * pParamSizeAdd );

void extractAndStoreArray_harness()
{
    DocParseErr_t err;
    OtaInterfaces_t otaInterface;

    const char * pKey;
    char * pValueInJson;
    size_t valueLength;
    void * pParamAdd;
    uint32_t pParamSizeAdd;

    /* Havoc otaAgent to non-deterministically set all the bytes in
     * the structure. */
    __CPROVER_havoc_object( &otaAgent );

    /* The maximum value of valueLength is OTA_DATA_BLOCK_SIZE which is enforced
     * in getFileContextFromJob function. */
    __CPROVER_assume( valueLength < OTA_DATA_BLOCK_SIZE );

    pParamAdd = ( uint8_t * ) malloc( ( valueLength + 1 ) * sizeof( char ) );
    pValueInJson = ( char * ) malloc( valueLength * sizeof( char ) );

    /* pValueInJson and pParamAdd are statically initialized in parseJSONbyModel. */
    __CPROVER_assume( pValueInJson != NULL );
    __CPROVER_assume( pParamAdd != NULL );

    /* CBMC preconditions. */
    otaInterface.os.mem.free = freeMemStub;
    otaInterface.os.mem.malloc = mallocMemStub;

    /* OtaInterfaces and the interfaces included in it cannot be NULL and they are checked
     * during the initialization of OTA specifically in the OTA_Init function. */
    otaAgent.pOtaInterface = &otaInterface;

    err = extractAndStoreArray( pKey, pValueInJson, valueLength, &pParamAdd, &pParamSizeAdd );

    /* The maximum returned by extractAndStoreArray is the length of the otaTransitionTable which
     * is defined by TRANSITION_TABLE_LEN in the Makefile. */
    __CPROVER_assert( ( err == DocParseErrNone ) || ( err == DocParseErrOutOfMemory ) ||
                      ( err == DocParseErrUserBufferInsuffcient ),
                      "Error: Return value from processValidFileContext should follow values of OtaErr_t enum." );

    free( pParamAdd );
    free( pValueInJson );
}
