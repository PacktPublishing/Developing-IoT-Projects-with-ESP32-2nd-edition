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

#ifndef CORE_JSON_ANNEX_H_
#define CORE_JSON_ANNEX_H_

#include <stdint.h>

#include "core_json.h"

#define isBool( x )           ( ( x == true ) || ( x == false ) )

/* parameter check fail values for JSON API functions */
#define parameterEnum( x )    ( ( x == JSONNullParameter ) || ( x == JSONBadParameter ) )

/* These 3 enums represent all the ways skipCollection() can fail. */
#define skipCollectionFailEnum( x ) \
    ( ( x == JSONPartial ) || ( x == JSONIllegalDocument ) || ( x == JSONMaxDepthExceeded ) )

/* All possible return values for skipCollection() */
#define skipCollectionEnum( x )    ( skipCollectionFailEnum( x ) || ( x == JSONSuccess ) )

/* All possible return values for JSON_Validate() */
#define jsonValidateEnum( x )      ( skipCollectionEnum( x ) || parameterEnum( x ) )

/* All possible return values for JSON_Search() */
#define jsonSearchEnum( x )        ( jsonValidateEnum( x ) || ( x == JSONNotFound ) )

/* All possible return values for JSON_Iterate() */
#define jsonIterateEnum( x )                                \
    ( parameterEnum( x ) || ( x == JSONIllegalDocument ) || \
      ( x == JSONNotFound ) || ( x == JSONSuccess ) )

/* All possible type values output from JSON_SearchT() */
#define jsonTypesEnum( x )   \
    ( ( x == JSONString ) || \
      ( x == JSONNumber ) || \
      ( x == JSONTrue ) ||   \
      ( x == JSONFalse ) ||  \
      ( x == JSONNull ) ||   \
      ( x == JSONObject ) || \
      ( x == JSONArray ) )

/*
 * These are declarations for the (normally) static functions from core_json.c.
 * Please see core_json.c for documentation.
 */

void skipSpace( const char * buf,
                size_t * start,
                size_t max );

bool skipUTF8( const char * buf,
               size_t * start,
               size_t max );

bool skipEscape( const char * buf,
                 size_t * start,
                 size_t max );

bool skipString( const char * buf,
                 size_t * start,
                 size_t max );

bool skipAnyLiteral( const char * buf,
                     size_t * start,
                     size_t max );

bool skipDigits( const char * buf,
                 size_t * start,
                 size_t max,
                 int32_t * outValue );

bool skipNumber( const char * buf,
                 size_t * start,
                 size_t max );

bool skipSpaceAndComma( const char * buf,
                        size_t * start,
                        size_t max );

bool skipAnyScalar( const char * buf,
                    size_t * start,
                    size_t max );

JSONStatus_t skipCollection( const char * buf,
                             size_t * start,
                             size_t max );

#endif /* ifndef CORE_JSON_ANNEX_H_ */
