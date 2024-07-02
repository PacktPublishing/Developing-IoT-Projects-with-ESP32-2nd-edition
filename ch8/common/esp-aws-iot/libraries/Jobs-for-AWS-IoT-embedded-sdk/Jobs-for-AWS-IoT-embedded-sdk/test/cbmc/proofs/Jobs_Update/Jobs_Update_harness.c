/*
 * AWS IoT Jobs v1.3.0
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
 * @file Jobs_Update_harness.c
 * @brief Implements the proof harness for Jobs_Update function.
 */

#include <stdlib.h>
#include "jobs_annex.h"

void harness()
{
    char * buffer;
    size_t bufferLength;
    const char * thingName;
    uint16_t thingNameLength;
    const char * jobId;
    uint16_t jobIdLength;
    size_t * outLength;
    JobsStatus_t ret;

    /* The buffer length must not exceed the maximum object size supported by CBMC. */
    __CPROVER_assume( bufferLength < CBMC_MAX_OBJECT_SIZE );
    buffer = malloc( bufferLength );

    /* The thing name length must not exceed unwindings. */
    __CPROVER_assume( thingNameLength <= THINGNAME_MAX_LENGTH );
    thingName = malloc( thingNameLength );

    /* The job ID length must not exceed unwindings. */
    __CPROVER_assume( jobIdLength <= JOBID_MAX_LENGTH );
    jobId = malloc( jobIdLength );

    outLength = malloc( sizeof( *outLength ) );

    ret = Jobs_Update( buffer,
                       bufferLength,
                       thingName,
                       thingNameLength,
                       jobId,
                       jobIdLength,
                       outLength );

    __CPROVER_assert( jobsUpdateEnum( ret ), "The return value is a subset of JobsStatus_t." );

    if( ( ret != JobsBadParameter ) && ( outLength != NULL ) )
    {
        __CPROVER_assert( ( *outLength < bufferLength ), "Buffer writes do not exceed buffer length." );

        __CPROVER_assert( ( buffer[ *outLength ] == '\0' ), "Buffer is NUL terminated." );
    }
}
