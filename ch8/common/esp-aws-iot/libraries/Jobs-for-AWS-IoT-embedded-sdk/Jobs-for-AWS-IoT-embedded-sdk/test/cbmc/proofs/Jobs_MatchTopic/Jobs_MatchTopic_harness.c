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
 * @file Jobs_MatchTopic_harness.c
 * @brief Implements the proof harness for Jobs_MatchTopic function.
 */

#include <stdlib.h>
#include "jobs_annex.h"

void harness()
{
    char * topic;
    size_t topicLength;
    const char * thingName;
    uint16_t thingNameLength;
    JobsTopic_t * outApi;
    char ** outJobId;
    uint16_t * outJobIdLength;
    JobsStatus_t ret;

    /* The buffer length must not exceed the maximum object size supported by CBMC. */
    __CPROVER_assume( topicLength < CBMC_MAX_BUFSIZE );
    topic = malloc( topicLength );

    /* The thing name length must not exceed unwindings. */
    __CPROVER_assume( thingNameLength <= THINGNAME_MAX_LENGTH );
    thingName = malloc( thingNameLength );

    outApi = malloc( sizeof( *outApi ) );
    outJobId = malloc( sizeof( *outJobId ) );
    outJobIdLength = malloc( sizeof( *outJobIdLength ) );

    ret = Jobs_MatchTopic( topic,
                           topicLength,
                           thingName,
                           thingNameLength,
                           outApi,
                           outJobId,
                           outJobIdLength );

    __CPROVER_assert( jobsMatchTopicEnum( ret ), "The return value is a subset of JobsStatus_t." );

    if( ret == JobsSuccess )
    {
        if( outApi != NULL )
        {
            __CPROVER_assert( jobsTopicEnum( *outApi ), "The API value is a JobsTopic_t enum." );
        }

        if( ( outJobId != NULL ) && ( *outJobId != NULL ) )
        {
            __CPROVER_assert( ( ( *outJobId > topic ) && ( *outJobId < ( topic + topicLength ) ) ),
                              "The output parameter for jobId points within the topic string." );
        }

        if( ( outJobIdLength != NULL ) && ( *outJobIdLength > 0 ) )
        {
            __CPROVER_assert( ( *outJobIdLength < topicLength ),
                              "The length of the jobId part of the topic is less than the length of the topic." );
        }
    }
}
