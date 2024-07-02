/*
 * coreJSON v1.0.0
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

#include "skipGeneric.h"

/*
 * This function is a replacement for the function of the same name from core_json.c.
 * Please see core_json.c for documentation.
 */

bool skipDigits( const char * buf,
                 size_t * start,
                 size_t max,
                 int32_t * outValue )
{
    /* min argument is 1 for a single digit, e.g., 0. */
    bool ret = skipGeneric( buf, start, max, 1 );

    if( ( ret == true ) && ( outValue != NULL ) )
    {
        int32_t x;
        __CPROVER_assume( x >= 0 );
        __CPROVER_assume( x <= MAX_INDEX_VALUE );

        *outValue = nondet_bool() ? x : -1;
    }

    return ret;
}
