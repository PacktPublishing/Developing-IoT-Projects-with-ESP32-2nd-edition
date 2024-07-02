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
 * @file JSON_Iterate_harness.c
 * @brief Implements the proof harness for the JSON_Iterate function.
 */

#include <stdlib.h>
#include "core_json_annex.h"

void harness()
{
    char * buf;
    size_t max;
    size_t * start, * next;
    JSONPair_t * pair;
    JSONStatus_t ret;

    /* max is the buffer length which must not exceed unwindings. */
    __CPROVER_assume( max < CBMC_MAX_BUFSIZE );

    buf = malloc( max );
    start = malloc( sizeof( *start ) );
    next = malloc( sizeof( *next ) );
    pair = malloc( sizeof( *pair ) );

    if( pair != NULL )
    {
        JSONPair_t tmp = { 0 };
        *pair = tmp;
    }

    ret = JSON_Iterate( buf,
                        max,
                        start,
                        next,
                        pair );

    __CPROVER_assert( jsonIterateEnum( ret ), "The return value is a JSONStatus_t." );

    if( ret == JSONSuccess )
    {
        if( pair->key != NULL )
        {
            __CPROVER_assert( ( pair->key > buf ) &&
                              ( ( pair->key + pair->keyLength ) < ( buf + max ) ),
                              "The output key is a sequence of characters within buf." );

            __CPROVER_assert( ( pair->key + pair->keyLength ) < pair->value,
                              "The output value occurs after the key." );
        }

        __CPROVER_assert( ( pair->value > buf ) &&
                          ( ( pair->value + pair->valueLength ) <= ( buf + max ) ),
                          "The output value is a sequence of characters within buf." );

        __CPROVER_assert( jsonTypesEnum( pair->jsonType ), "The value type is a JSONTypes_t." );
    }
}
