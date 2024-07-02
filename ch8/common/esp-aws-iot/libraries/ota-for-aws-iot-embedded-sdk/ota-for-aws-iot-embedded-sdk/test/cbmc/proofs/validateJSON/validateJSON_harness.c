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
 * @file validateJSON_harness.c
 * @brief Implements the proof harness for validateJSON function.
 */
/*  Ota Agent includes. */
#include "ota.h"
#include "core_json.h"
#include <stdlib.h>

/* validateJSON is a static function in ota.c and to expose the function to a different file
 * CBMC mangles the name and it is required to have a declaration of the test function with the
 * mangled name. */
DocParseErr_t __CPROVER_file_local_ota_c_validateJSON( const char * pJson,
                                                       uint32_t messageLength );

/* Stub to validate the json string. */
JSONStatus_t JSON_Validate( const char * buf,
                            size_t max )
{
    JSONStatus_t status;

    __CPROVER_assume( ( status >= JSONPartial ) && ( status <= JSONBadParameter ) );
    return status;
}

void validateJSON_harness()
{
    DocParseErr_t err;
    char * pJson;
    uint32_t messageLength;

    /* pJson is a json string of size messageLength. */
    pJson = ( char * ) malloc( sizeof( char ) * messageLength );

    err = __CPROVER_file_local_ota_c_validateJSON( pJson, messageLength );

    __CPROVER_assert( ( err == DocParseErrNone ) || ( err <= DocParseErrNullDocPointer ) ||
                      ( err <= DocParseErr_InvalidJSONBuffer ),
                      "Error: Return value from validateJSON should follow values of DocParseErr_t enum." );

    free( pJson );
}
