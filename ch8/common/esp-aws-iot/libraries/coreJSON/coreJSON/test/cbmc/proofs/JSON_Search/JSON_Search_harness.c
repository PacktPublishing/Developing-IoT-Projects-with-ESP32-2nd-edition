/*
 * coreJSON v3.2.0
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * @file JSON_Search_harness.c
 * @brief Implements the proof harness for the JSON_Search function.
 */

#include <stdlib.h>
#include "core_json_annex.h"

void harness()
{
    char * buf = NULL;
    size_t max;
    char * query = NULL;
    size_t queryLength;
    char * outValue;
    size_t outValueLength;
    JSONStatus_t ret;
    JSONTypes_t outType;

    /* max is the buffer length which must not exceed unwindings. */
    __CPROVER_assume( max < CBMC_MAX_BUFSIZE );

    if( nondet_bool() )
    {
        buf = malloc( max );
    }

    /* queryLength is the buffer length of the query which must not exceed unwindings. */
    __CPROVER_assume( queryLength < CBMC_MAX_QUERYKEYLENGTH );

    if( nondet_bool() )
    {
        query = malloc( queryLength );
    }

    ret = JSON_SearchT( buf,
                        max,
                        query,
                        queryLength,
                        ( nondet_bool() ? &outValue : NULL ),
                        ( nondet_bool() ? &outValueLength : NULL ),
                        ( nondet_bool() ? &outType : NULL ) );

    __CPROVER_assert( jsonSearchEnum( ret ), "The return value is a JSONStatus_t." );

    if( ret == JSONSuccess )
    {
        __CPROVER_assert( ( outValue >= buf ) &&
                          ( ( outValue + outValueLength ) <= ( buf + max ) ),
                          "The output value is a sequence of characters within buf." );

        __CPROVER_assert( jsonTypesEnum( ret ), "The value type is a JSONTypes_t." );
    }
}
