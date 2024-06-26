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
 * @file skipNumber_harness.c
 * @brief Implements the proof harness for the skipNumber function.
 */

#include <stdlib.h>
#include "core_json_annex.h"

void harness()
{
    char * buf;
    size_t start, max;
    bool ret;
    int32_t * outValue;

    /* max is the buffer length which must be nonzero for non-API functions. */
    __CPROVER_assume( max > 0 );

    /* max is the buffer length which must not exceed unwindings. */
    __CPROVER_assume( max < CBMC_MAX_BUFSIZE );

    /* buf must not be NULL */
    buf = malloc( max );
    __CPROVER_assume( buf != NULL );

    ret = skipNumber( buf, &start, max );

    __CPROVER_assert( isBool( ret ), "A bool value is returned." );

    if( ret == true )
    {
        __CPROVER_assert( start <= max,
                          "The buffer start index does not exceed the buffer length." );
    }

    /* outValue may be NULL */
    outValue = malloc( sizeof( *outValue ) );

    ret = skipDigits( buf, &start, max, outValue );

    __CPROVER_assert( isBool( ret ), "A bool value is returned." );

    if( ( ret == true ) && ( outValue != NULL ) )
    {
        __CPROVER_assert( ( ( *outValue == -1 ) || ( ( *outValue >= 0 ) && ( *outValue <= MAX_INDEX_VALUE ) ) ),
                          "The converted integer is within the permitted range or is -1." );
    }
}
