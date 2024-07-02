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
 * @file jobs.c
 * @brief Implementation of the APIs from jobs.h.
 */

#include <assert.h>

#include "jobs.h"

/** @cond DO_NOT_DOCUMENT */

typedef enum
{
    true = 1, false = 0
} bool_;

/**
 * @brief Table of topic API strings in JobsTopic_t order.
 */
static const char * const apiTopic[] =
{
    JOBS_API_JOBSCHANGED,
    JOBS_API_NEXTJOBCHANGED,
    JOBS_API_GETPENDING JOBS_API_SUCCESS,
    JOBS_API_GETPENDING JOBS_API_FAILURE,
    JOBS_API_STARTNEXT JOBS_API_SUCCESS,
    JOBS_API_STARTNEXT JOBS_API_FAILURE,
    JOBS_API_DESCRIBE JOBS_API_SUCCESS,
    JOBS_API_DESCRIBE JOBS_API_FAILURE,
    JOBS_API_UPDATE JOBS_API_SUCCESS,
    JOBS_API_UPDATE JOBS_API_FAILURE,
};

/**
 * @brief Table of topic API string lengths in JobsTopic_t order.
 */
static const size_t apiTopicLength[] =
{
    JOBS_API_JOBSCHANGED_LENGTH,
    JOBS_API_NEXTJOBCHANGED_LENGTH,
    JOBS_API_GETPENDING_LENGTH + JOBS_API_SUCCESS_LENGTH,
    JOBS_API_GETPENDING_LENGTH + JOBS_API_FAILURE_LENGTH,
    JOBS_API_STARTNEXT_LENGTH + JOBS_API_SUCCESS_LENGTH,
    JOBS_API_STARTNEXT_LENGTH + JOBS_API_FAILURE_LENGTH,
    JOBS_API_DESCRIBE_LENGTH + JOBS_API_SUCCESS_LENGTH,
    JOBS_API_DESCRIBE_LENGTH + JOBS_API_FAILURE_LENGTH,
    JOBS_API_UPDATE_LENGTH + JOBS_API_SUCCESS_LENGTH,
    JOBS_API_UPDATE_LENGTH + JOBS_API_FAILURE_LENGTH,
};

/**
 * @brief Predicate returns true for a valid thing name or job ID character.
 *
 * @param[in] a  character to check
 * @param[in] allowColon  set to true for thing names
 *
 * @return true if the character is valid;
 * false otherwise
 */
static bool_ isValidChar( char a,
                          bool_ allowColon )
{
    bool_ ret;

    if( ( a == '-' ) || ( a == '_' ) )
    {
        ret = true;
    }
    else if( ( a >= '0' ) && ( a <= '9' ) )
    {
        ret = true;
    }
    else if( ( a >= 'A' ) && ( a <= 'Z' ) )
    {
        ret = true;
    }
    else if( ( a >= 'a' ) && ( a <= 'z' ) )
    {
        ret = true;
    }
    else if( a == ':' )
    {
        ret = allowColon;
    }
    else
    {
        ret = false;
    }

    return ret;
}

/**
 * @brief Predicate returns true for a valid identifier.
 *
 * The identifier may be a thing name or a job ID.
 *
 * @param[in] id  character sequence to check
 * @param[in] length  length of the character sequence
 * @param[in] max  maximum length of a valid identifier
 * @param[in] allowColon  set to true for thing names
 *
 * @return true if the identifier is valid;
 * false otherwise
 */
static bool_ isValidID( const char * id,
                        uint16_t length,
                        uint16_t max,
                        bool_ allowColon )
{
    bool_ ret = false;

    if( ( id != NULL ) && ( length > 0U ) &&
        ( length <= max ) )
    {
        size_t i;

        for( i = 0; i < length; i++ )
        {
            if( isValidChar( id[ i ], allowColon ) == false )
            {
                break;
            }
        }

        ret = ( i == length ) ? true : false;
    }

    return ret;
}


/**
 * @brief Predicate returns true for a valid thing name string.
 *
 * @param[in] thingName  character sequence to check
 * @param[in] thingNameLength  length of the character sequence
 *
 * @return true if the thing name is valid;
 * false otherwise
 */
static bool_ isValidThingName( const char * thingName,
                               uint16_t thingNameLength )
{
    return isValidID( thingName, thingNameLength,
                      THINGNAME_MAX_LENGTH, true );
}

/**
 * @brief Predicate returns true for a valid job ID string.
 *
 * @param[in] jobId  character sequence to check
 * @param[in] jobIdLength  length of the character sequence
 *
 * @return true if the job ID is valid;
 * false otherwise
 */
static bool_ isValidJobId( const char * jobId,
                           uint16_t jobIdLength )
{
    return isValidID( jobId, jobIdLength,
                      JOBID_MAX_LENGTH, false );
}

/**
 * @brief A strncpy replacement based on lengths only.
 *
 * @param[in] buffer  The buffer to be written.
 * @param[in,out] start  The index at which to begin.
 * @param[in] max  The size of the buffer.
 * @param[in] value  The characters to copy.
 * @param[in] valueLength  How many characters to copy.
 *
 * @return #JobsSuccess if the value was written to the buffer;
 * #JobsBufferTooSmall if the buffer cannot hold the entire value.
 *
 * @note There is no harm from calling this function when
 * start >= max.  This allows for sequential calls to
 * strnAppend() where only the final call's return value
 * is needed.
 */
static JobsStatus_t strnAppend( char * buffer,
                                size_t * start,
                                size_t max,
                                const char * value,
                                size_t valueLength )
{
    size_t i, j = 0;

    assert( ( buffer != NULL ) && ( start != NULL ) && ( value != NULL ) );

    i = *start;

    while( ( i < max ) && ( j < valueLength ) )
    {
        buffer[ i ] = value[ j ];
        i++;
        j++;
    }

    *start = i;

    return ( i < max ) ? JobsSuccess : JobsBufferTooSmall;
}

/**
 * @brief Populate the common leading portion of a topic string.
 *
 * @param[in] buffer  The buffer to contain the topic string.
 * @param[in,out] start  The index at which to begin.
 * @param[in] length  The size of the buffer.
 * @param[in] thingName  The device's thingName as registered with AWS IoT.
 * @param[in] thingNameLength  The length of the thingName.
 */
static void writePreamble( char * buffer,
                           size_t * start,
                           size_t length,
                           const char * thingName,
                           uint16_t thingNameLength )
{
    ( void ) strnAppend( buffer, start, length,
                         JOBS_API_PREFIX, JOBS_API_PREFIX_LENGTH );
    ( void ) strnAppend( buffer, start, length,
                         thingName, thingNameLength );
    ( void ) strnAppend( buffer, start, length,
                         JOBS_API_BRIDGE, JOBS_API_BRIDGE_LENGTH );
}

#define checkThingParams() \
    ( isValidThingName( thingName, thingNameLength ) == true )

#define checkCommonParams() \
    ( ( buffer != NULL ) && ( length > 0U ) && checkThingParams() )

/** @endcond */

/**
 * See jobs.h for docs.
 *
 * @brief Populate a topic string for a subscription request.
 */
JobsStatus_t Jobs_GetTopic( char * buffer,
                            size_t length,
                            const char * thingName,
                            uint16_t thingNameLength,
                            JobsTopic_t api,
                            size_t * outLength )
{
    JobsStatus_t ret = JobsBadParameter;
    size_t start = 0U;

    if( checkCommonParams() &&
        ( api > JobsInvalidTopic ) && ( api < JobsMaxTopic ) )
    {
        writePreamble( buffer, &start, length, thingName, thingNameLength );

        if( api >= JobsDescribeSuccess )
        {
            ( void ) strnAppend( buffer, &start, length,
                                 "+/", ( sizeof( "+/" ) - 1U ) );
        }

        ret = strnAppend( buffer, &start, length,
                          apiTopic[ api ], apiTopicLength[ api ] );

        if( start == length )
        {
            start--;
        }

        buffer[ start ] = '\0';

        if( outLength != NULL )
        {
            *outLength = start;
        }
    }

    return ret;
}

/** @cond DO_NOT_DOCUMENT */

/**
 * @brief Compare the leading n bytes of two character sequences.
 *
 * @param[in] a  first character sequence
 * @param[in] b  second character sequence
 * @param[in] n  number of bytes
 *
 * @return JobsSuccess if the sequences are the same;
 * JobsNoMatch otherwise
 */
static JobsStatus_t strnEq( const char * a,
                            const char * b,
                            size_t n )
{
    size_t i;

    assert( ( a != NULL ) && ( b != NULL ) );

    for( i = 0U; i < n; i++ )
    {
        if( a[ i ] != b[ i ] )
        {
            break;
        }
    }

    return ( i == n ) ? JobsSuccess : JobsNoMatch;
}

/**
 * @brief Wrap strnEq() with a check to compare two lengths.
 *
 * @param[in] a  first character sequence
 * @param[in] aLength  Length of a
 * @param[in] b  second character sequence
 * @param[in] bLength  Length of b
 *
 * @return JobsSuccess if the sequences are the same;
 * JobsNoMatch otherwise
 */
static JobsStatus_t strnnEq( const char * a,
                             size_t aLength,
                             const char * b,
                             size_t bLength )
{
    JobsStatus_t ret = JobsNoMatch;

    if( aLength == bLength )
    {
        ret = strnEq( a, b, aLength );
    }

    return ret;
}

/**
 * @brief Predicate returns true for a match to JOBS_API_JOBID_NEXT
 *
 * @param[in] jobId  character sequence to check
 * @param[in] jobIdLength  length of the character sequence
 *
 * @return true if the job ID matches;
 * false otherwise
 */
static bool_ isNextJobId( const char * jobId,
                          uint16_t jobIdLength )
{
    bool_ ret = false;

    if( ( jobId != NULL ) &&
        ( strnnEq( JOBS_API_JOBID_NEXT, JOBS_API_JOBID_NEXT_LENGTH, jobId, jobIdLength ) == JobsSuccess ) )
    {
        ret = true;
    }

    return ret;
}


/**
 * @brief Parse a job ID and search for the API portion of a topic string in a table.
 *
 * @param[in] topic  The topic string to check.
 * @param[in] topicLength  The length of the topic string.
 * @param[out] outApi  The jobs topic API value if present, e.g., #JobsUpdateSuccess.
 * @param[out] outJobId  The beginning of the jobID in the topic string.
 * @param[out] outJobIdLength  The length of the jobID in the topic string.
 *
 * @return #JobsSuccess if a matching topic was found;
 * #JobsNoMatch if a matching topic was NOT found
 *   (parameter outApi gets #JobsInvalidTopic ).
 */
static JobsStatus_t matchIdApi( char * topic,
                                size_t topicLength,
                                JobsTopic_t * outApi,
                                char ** outJobId,
                                uint16_t * outJobIdLength )
{
    JobsStatus_t ret = JobsNoMatch;
    size_t i;
    char * p = topic;
    size_t length = topicLength;
    char * jobId = NULL;
    uint16_t jobIdLength = 0U;

    assert( ( topic != NULL ) && ( outApi != NULL ) &&
            ( outJobId != NULL ) && ( outJobIdLength != NULL ) );

    for( i = 0U; i < length; i++ )
    {
        if( ( i > 0U ) && ( p[ i ] == '/' ) )
        {
            /* Save the leading job ID and its length. */
            jobId = p;
            jobIdLength = ( uint16_t ) i;
            break;
        }
    }

    /* Advance p to after the '/' and reduce buffer length
     * for the remaining API search. */
    p = &p[ jobIdLength + 1U ];
    length = length - jobIdLength - 1U;

    if( ( isNextJobId( jobId, jobIdLength ) == true ) ||
        ( isValidJobId( jobId, jobIdLength ) == true ) )
    {
        if( JobsSuccess == strnnEq( p, length, apiTopic[ JobsDescribeSuccess ], apiTopicLength[ JobsDescribeSuccess ] ) )
        {
            ret = JobsSuccess;
            *outApi = JobsDescribeSuccess;
        }
        else if( JobsSuccess == strnnEq( p, length, apiTopic[ JobsDescribeFailed ], apiTopicLength[ JobsDescribeFailed ] ) )
        {
            ret = JobsSuccess;
            *outApi = JobsDescribeFailed;
        }
        else if( JobsSuccess == strnnEq( p, length, apiTopic[ JobsUpdateSuccess ], apiTopicLength[ JobsUpdateSuccess ] ) )
        {
            ret = JobsSuccess;
            *outApi = JobsUpdateSuccess;
        }
        else if( JobsSuccess == strnnEq( p, length, apiTopic[ JobsUpdateFailed ], apiTopicLength[ JobsUpdateFailed ] ) )
        {
            ret = JobsSuccess;
            *outApi = JobsUpdateFailed;
        }
        else
        {
            /* MISRA Empty Body */
        }

        if( ret == JobsSuccess )
        {
            *outJobId = jobId;
            *outJobIdLength = jobIdLength;
        }
    }

    return ret;
}

/**
 * @brief Search for the API portion of a topic string in a table.
 *
 * @param[in] topic  The topic string to check.
 * @param[in] topicLength  The length of the topic string.
 * @param[out] outApi  The jobs topic API value if present, e.g., #JobsUpdateSuccess.
 * @param[out] outJobId  The beginning of the jobID in the topic string.
 * @param[out] outJobIdLength  The length of the jobID in the topic string.
 *
 * @return #JobsSuccess if a matching topic was found;
 * #JobsNoMatch if a matching topic was NOT found
 *   (parameter outApi gets #JobsInvalidTopic ).
 */
static JobsStatus_t matchApi( char * topic,
                              size_t topicLength,
                              JobsTopic_t * outApi,
                              char ** outJobId,
                              uint16_t * outJobIdLength )
{
    JobsStatus_t ret = JobsNoMatch;

    assert( ( topic != NULL ) && ( outApi != NULL ) &&
            ( outJobId != NULL ) && ( outJobIdLength != NULL ) );

    /* The first set of APIs do not have job IDs. */
    if( JobsSuccess == strnnEq( topic, topicLength, apiTopic[ JobsJobsChanged ], apiTopicLength[ JobsJobsChanged ] ) )
    {
        ret = JobsSuccess;
        *outApi = JobsJobsChanged;
    }
    else if( JobsSuccess == strnnEq( topic, topicLength, apiTopic[ JobsNextJobChanged ], apiTopicLength[ JobsNextJobChanged ] ) )
    {
        ret = JobsSuccess;
        *outApi = JobsNextJobChanged;
    }
    else if( JobsSuccess == strnnEq( topic, topicLength, apiTopic[ JobsGetPendingSuccess ], apiTopicLength[ JobsGetPendingSuccess ] ) )
    {
        ret = JobsSuccess;
        *outApi = JobsGetPendingSuccess;
    }
    else if( JobsSuccess == strnnEq( topic, topicLength, apiTopic[ JobsGetPendingFailed ], apiTopicLength[ JobsGetPendingFailed ] ) )
    {
        ret = JobsSuccess;
        *outApi = JobsGetPendingFailed;
    }
    else if( JobsSuccess == strnnEq( topic, topicLength, apiTopic[ JobsStartNextSuccess ], apiTopicLength[ JobsStartNextSuccess ] ) )
    {
        ret = JobsSuccess;
        *outApi = JobsStartNextSuccess;
    }
    else if( JobsSuccess == strnnEq( topic, topicLength, apiTopic[ JobsStartNextFailed ], apiTopicLength[ JobsStartNextFailed ] ) )
    {
        ret = JobsSuccess;
        *outApi = JobsStartNextFailed;
    }
    else
    {
        /* MISRA Empty Body */
    }

    /* The remaining APIs must have a job ID. */
    if( ret == JobsNoMatch )
    {
        ret = matchIdApi( topic, topicLength, outApi, outJobId, outJobIdLength );
    }

    return ret;
}

/** @endcond */

/**
 * See jobs.h for docs.
 *
 * @brief Output a topic value if a Jobs API topic string is present.
 */
JobsStatus_t Jobs_MatchTopic( char * topic,
                              size_t length,
                              const char * thingName,
                              uint16_t thingNameLength,
                              JobsTopic_t * outApi,
                              char ** outJobId,
                              uint16_t * outJobIdLength )
{
    JobsStatus_t ret = JobsBadParameter;
    JobsTopic_t api = JobsInvalidTopic;
    char * jobId = NULL;
    uint16_t jobIdLength = 0U;

    if( ( topic != NULL ) && ( outApi != NULL ) && checkThingParams() && ( length > 0U ) )
    {
        ret = JobsNoMatch;

        if( ( length > JOBS_API_COMMON_LENGTH( thingNameLength ) ) &&
            ( length < JOBS_API_MAX_LENGTH( thingNameLength ) ) )
        {
            char * prefix = topic;
            char * name = &prefix[ JOBS_API_PREFIX_LENGTH ];
            char * bridge = &name[ thingNameLength ];

            /* check the shortest match first */
            if( ( strnEq( bridge, JOBS_API_BRIDGE, JOBS_API_BRIDGE_LENGTH ) == JobsSuccess ) &&
                ( strnEq( prefix, JOBS_API_PREFIX, JOBS_API_PREFIX_LENGTH ) == JobsSuccess ) &&
                ( strnEq( name, thingName, thingNameLength ) == JobsSuccess ) )
            {
                char * tail = &bridge[ JOBS_API_BRIDGE_LENGTH ];
                size_t tailLength = length - JOBS_API_COMMON_LENGTH( thingNameLength );

                ret = matchApi( tail, tailLength, &api, &jobId, &jobIdLength );
            }
        }
    }

    if( outApi != NULL )
    {
        *outApi = api;
    }

    if( outJobId != NULL )
    {
        *outJobId = jobId;
    }

    if( outJobIdLength != NULL )
    {
        *outJobIdLength = jobIdLength;
    }

    return ret;
}

/**
 * See jobs.h for docs.
 *
 * @brief Populate a topic string for a GetPendingJobExecutions request.
 */
JobsStatus_t Jobs_GetPending( char * buffer,
                              size_t length,
                              const char * thingName,
                              uint16_t thingNameLength,
                              size_t * outLength )
{
    JobsStatus_t ret = JobsBadParameter;
    size_t start = 0U;

    if( checkCommonParams() )
    {
        writePreamble( buffer, &start, length, thingName, thingNameLength );

        ret = strnAppend( buffer, &start, length,
                          JOBS_API_GETPENDING, JOBS_API_GETPENDING_LENGTH );

        start = ( start >= length ) ? ( length - 1U ) : start;
        buffer[ start ] = '\0';

        if( outLength != NULL )
        {
            *outLength = start;
        }
    }

    return ret;
}

/**
 * See jobs.h for docs.
 *
 * @brief Populate a topic string for a StartNextPendingJobExecution request.
 */
JobsStatus_t Jobs_StartNext( char * buffer,
                             size_t length,
                             const char * thingName,
                             uint16_t thingNameLength,
                             size_t * outLength )
{
    JobsStatus_t ret = JobsBadParameter;
    size_t start = 0U;

    if( checkCommonParams() )
    {
        writePreamble( buffer, &start, length, thingName, thingNameLength );

        ret = strnAppend( buffer, &start, length,
                          JOBS_API_STARTNEXT, JOBS_API_STARTNEXT_LENGTH );

        start = ( start >= length ) ? ( length - 1U ) : start;
        buffer[ start ] = '\0';

        if( outLength != NULL )
        {
            *outLength = start;
        }
    }

    return ret;
}


/**
 * See jobs.h for docs.
 *
 * @brief Populate a topic string for a DescribeJobExecution request.
 */
JobsStatus_t Jobs_Describe( char * buffer,
                            size_t length,
                            const char * thingName,
                            uint16_t thingNameLength,
                            const char * jobId,
                            uint16_t jobIdLength,
                            size_t * outLength )
{
    JobsStatus_t ret = JobsBadParameter;
    size_t start = 0U;

    if( checkCommonParams() &&
        ( ( isNextJobId( jobId, jobIdLength ) == true ) ||
          ( isValidJobId( jobId, jobIdLength ) == true ) ) )
    {
        writePreamble( buffer, &start, length, thingName, thingNameLength );

        ( void ) strnAppend( buffer, &start, length,
                             jobId, jobIdLength );
        ( void ) strnAppend( buffer, &start, length,
                             "/", ( sizeof( "/" ) - 1U ) );
        ret = strnAppend( buffer, &start, length,
                          JOBS_API_DESCRIBE, JOBS_API_DESCRIBE_LENGTH );

        start = ( start >= length ) ? ( length - 1U ) : start;
        buffer[ start ] = '\0';

        if( outLength != NULL )
        {
            *outLength = start;
        }
    }

    return ret;
}

/**
 * See jobs.h for docs.
 *
 * @brief Populate a topic string for an UpdateJobExecution request.
 */
JobsStatus_t Jobs_Update( char * buffer,
                          size_t length,
                          const char * thingName,
                          uint16_t thingNameLength,
                          const char * jobId,
                          uint16_t jobIdLength,
                          size_t * outLength )
{
    JobsStatus_t ret = JobsBadParameter;
    size_t start = 0U;

    if( checkCommonParams() &&
        ( isValidJobId( jobId, jobIdLength ) == true ) )
    {
        writePreamble( buffer, &start, length, thingName, thingNameLength );

        ( void ) strnAppend( buffer, &start, length,
                             jobId, jobIdLength );
        ( void ) strnAppend( buffer, &start, length,
                             "/", ( sizeof( "/" ) - 1U ) );
        ret = strnAppend( buffer, &start, length,
                          JOBS_API_UPDATE, JOBS_API_UPDATE_LENGTH );

        start = ( start >= length ) ? ( length - 1U ) : start;
        buffer[ start ] = '\0';

        if( outLength != NULL )
        {
            *outLength = start;
        }
    }

    return ret;
}
