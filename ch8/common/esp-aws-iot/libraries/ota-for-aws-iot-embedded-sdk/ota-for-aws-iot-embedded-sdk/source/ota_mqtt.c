/*
 * AWS IoT Over-the-air Update v3.4.0
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
 * @file ota_mqtt.c
 * @brief Routines for supporting over the air updates using MQTT.
 */

/* Standard includes. */
#include <string.h>
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

/* OTA includes. */
#include "ota.h"
#include "ota_private.h"
#include "ota_cbor_private.h"

/* Private include. */
#include "ota_mqtt_private.h"

/* Include firmware version struct definition. */
#include "ota_appversion32.h"

/* Stream GET message constants. */
#define OTA_CLIENT_TOKEN             "rdy"                  /*!< Arbitrary client token sent in the stream "GET" message. */

/* Agent to Job Service status message constants. */
#define OTA_STATUS_MSG_MAX_SIZE      128U               /*!< Max length of a job status message to the service. */

/**
 *  @brief Topic strings used by the OTA process.
 *
 * These first few are topic extensions to the dynamic base topic that includes the Thing name.
 */
#define MQTT_API_THINGS              "$aws/things/"                   /*!< Topic prefix for thing APIs. */
#define MQTT_API_JOBS_NEXT_GET       "/jobs/$next/get"                /*!< Topic suffix for job API. */
#define MQTT_API_JOBS_NOTIFY_NEXT    "/jobs/notify-next"              /*!< Topic suffix for job API. */
#define MQTT_API_JOBS                "/jobs/"                         /*!< Job API identifier. */
#define MQTT_API_UPDATE              "/update"                        /*!< Job API identifier. */
#define MQTT_API_STREAMS             "/streams/"                      /*!< Stream API identifier. */
#define MQTT_API_DATA_CBOR           "/data/cbor"                     /*!< Stream API suffix. */
#define MQTT_API_GET_CBOR            "/get/cbor"                      /*!< Stream API suffix. */

/* NOTE: The format specifiers in this string are placeholders only; the lengths of these
 * strings are used to calculate buffer sizes.
 */
static const char pOtaJobsGetNextTopicTemplate[] = MQTT_API_THINGS "%s"MQTT_API_JOBS_NEXT_GET;                 /*!< Topic template to request next job. */
static const char pOtaJobsNotifyNextTopicTemplate[] = MQTT_API_THINGS "%s"MQTT_API_JOBS_NOTIFY_NEXT;           /*!< Topic template to notify next . */
static const char pOtaJobStatusTopicTemplate[] = MQTT_API_THINGS "%s"MQTT_API_JOBS "%s"MQTT_API_UPDATE;        /*!< Topic template to update the current job. */
static const char pOtaStreamDataTopicTemplate[] = MQTT_API_THINGS "%s"MQTT_API_STREAMS "%s"MQTT_API_DATA_CBOR; /*!< Topic template to receive data over a stream. */
static const char pOtaGetStreamTopicTemplate[] = MQTT_API_THINGS "%s"MQTT_API_STREAMS "%s"MQTT_API_GET_CBOR;   /*!< Topic template to request next data over a stream. */

static const char pOtaGetNextJobMsgTemplate[] = "{\"clientToken\":\"%u:%s\"}";                                 /*!< Used to specify client token id to authenticate job. */
static const char pOtaStringReceive[] = "\"receive\"";                                                         /*!< Used to build the job receive template. */

/** We map all of the above status cases to one of these status strings.
 * These are the only strings that are supported by the Job Service. You
 * shall not change them to arbitrary strings or the job will not change
 * states.
 * */
#define JOBS_API_STATUS_IN_PROGRESS    "IN_PROGRESS" /*!< The job document has be received on the device and update is in progress. */
#define JOBS_API_STATUS_FAILED         "FAILED"      /*!< OTA update failed due to an error. */
#define JOBS_API_STATUS_SUCCEEDED      "SUCCEEDED"   /*!< OTA update succeeded. */
#define JOBS_API_STATUS_REJECTED       "REJECTED"    /*!< The job was rejected due to invalid parameters. */

/**
 * @brief List of all the status cases a job can be in.
 *
 */
static const char * pOtaJobStatusStrings[ NumJobStatusMappings ] =
{
    "{\"status\":\""JOBS_API_STATUS_IN_PROGRESS "\",\"statusDetails\":{",
    "{\"status\":\""JOBS_API_STATUS_FAILED "\",\"statusDetails\":{",
    "{\"status\":\""JOBS_API_STATUS_SUCCEEDED "\",\"statusDetails\":{",
    "{\"status\":\""JOBS_API_STATUS_REJECTED "\",\"statusDetails\":{",
    "{\"status\":\""JOBS_API_STATUS_FAILED "\",\"statusDetails\":{", /* eJobStatus_FailedWithVal */
};

/**
 * @brief These are the associated statusDetails 'reason' codes that go along with
 * the above enums during the OTA update process. The 'Receiving' state is
 * updated with transfer progress as number of blocks received of total blocks.
 *
 */
static const char * pOtaJobReasonStrings[ NumJobReasons ] = { "", "ready", "active", "accepted", "rejected", "aborted" };

/**
 * @brief These are used for both decimal and hex string conversions.
 */
static const char asciiDigits[] =
{
    '0', '1', '2', '3',
    '4', '5', '6', '7',
    '8', '9', 'a', 'b',
    'c', 'd', 'e', 'f',
};

/* Maximum lengths for constants used in the ota_mqtt_topic_strings templates.
 * These are used to calculate the static size of buffers used to store MQTT
 * topic and message strings. Each length is in terms of bytes. */
#define U32_MAX_LEN            10U                                              /*!< Maximum number of output digits of an unsigned long value. */
#define JOB_NAME_MAX_LEN       128U                                             /*!< Maximum length of the name of job documents received from the server. */
#define STREAM_NAME_MAX_LEN    44U                                              /*!< Maximum length for the name of MQTT streams. */
#define NULL_CHAR_LEN          1U                                               /*!< Size of a single null character used to terminate topics and messages. */

/* Pre-calculate max buffer size for mqtt topics and messages. We make sure the buffer size is large
 * enough to hold a dynamically constructed topic and message string.
 */
#define TOPIC_PLUS_THINGNAME_LEN( topic )    ( CONST_STRLEN( topic ) + otaconfigMAX_THINGNAME_LEN + NULL_CHAR_LEN )              /*!< Calculate max buffer size based on topic template and thing name length. */
#define TOPIC_GET_NEXT_BUFFER_SIZE       ( TOPIC_PLUS_THINGNAME_LEN( pOtaJobsGetNextTopicTemplate ) )                            /*!< Max buffer size for `jobs/$next/get` topic. */
#define TOPIC_NOTIFY_NEXT_BUFFER_SIZE    ( TOPIC_PLUS_THINGNAME_LEN( pOtaJobsNotifyNextTopicTemplate ) )                         /*!< Max buffer size for `jobs/notify-next` topic. */
#define TOPIC_JOB_STATUS_BUFFER_SIZE     ( TOPIC_PLUS_THINGNAME_LEN( pOtaJobStatusTopicTemplate ) + JOB_NAME_MAX_LEN )           /*!< Max buffer size for `jobs/<job_name>/update` topic. */
#define TOPIC_STREAM_DATA_BUFFER_SIZE    ( TOPIC_PLUS_THINGNAME_LEN( pOtaStreamDataTopicTemplate ) + STREAM_NAME_MAX_LEN )       /*!< Max buffer size for `streams/<stream_name>/data/cbor` topic. */
#define TOPIC_GET_STREAM_BUFFER_SIZE     ( TOPIC_PLUS_THINGNAME_LEN( pOtaGetStreamTopicTemplate ) + STREAM_NAME_MAX_LEN )        /*!< Max buffer size for `streams/<stream_name>/get/cbor` topic. */
#define MSG_GET_NEXT_BUFFER_SIZE         ( TOPIC_PLUS_THINGNAME_LEN( pOtaGetNextJobMsgTemplate ) + U32_MAX_LEN )                 /*!< Max buffer size for message of `jobs/$next/get topic`. */

/**
 * @brief Subscribe to the jobs notification topic (i.e. New file version available).
 *
 * @param[in] pAgentCtx Agent context which stores the thing details and mqtt interface.
 * @return OtaMqttStatus_t Result of the subscribe operation, OtaMqttSuccess if the operation is successful
 */
static OtaMqttStatus_t subscribeToJobNotificationTopics( const OtaAgentContext_t * pAgentCtx );

/**
 * @brief UnSubscribe from the firmware update receive topic.
 *
 * @param[in] pAgentCtx Agent context which stores the thing details and mqtt interface.
 * @return OtaMqttStatus_t Result of the unsubscribe operation, OtaMqttSuccess if the operation is successful.
 */
static OtaMqttStatus_t unsubscribeFromDataStream( const OtaAgentContext_t * pAgentCtx );

/**
 * @brief UnSubscribe from the jobs notification topic.
 *
 * @param[in] pAgentCtx Agent context which stores the thing details and mqtt interface.
 * @return OtaMqttStatus_t Result of the unsubscribe operation, OtaMqttSuccess if the operation is successful.
 */
static OtaMqttStatus_t unsubscribeFromJobNotificationTopic( const OtaAgentContext_t * pAgentCtx );

/**
 * @brief Publish a message to the job status topic.
 *
 * @param[in] pAgentCtx Agent context which provides the details for the thing, job and mqtt interface.
 * @param[in] pMsg Message to publish.
 * @param[in] msgSize Size of message to send.
 * @param[in] qos Quality of service level for mqtt.
 * @return OtaMqttStatus_t OtaMqttSuccess if the message is publish is successful.
 */
static OtaMqttStatus_t publishStatusMessage( const OtaAgentContext_t * pAgentCtx,
                                             const char * pMsg,
                                             uint32_t msgSize,
                                             uint8_t qos );

/**
 * @brief Populate the message buffer with the job status message.
 *
 * @param[in] pMsgBuffer Buffer to populate.
 * @param[in] msgBufferSize Size of the message.
 * @param[in] status Status of the operation.
 * @param[in] pOTAFileCtx File context stores the information about the downloaded blocks and required size.
 * @return uint32_t Size of the message built.
 */
static uint32_t buildStatusMessageReceiving( char * pMsgBuffer,
                                             size_t msgBufferSize,
                                             OtaJobStatus_t status,
                                             const OtaFileContext_t * pOTAFileCtx );

/**
 * @brief Populate the message buffer with the message to indicate device in self-test.
 *
 * @param[in] pMsgBuffer Buffer to populate.
 * @param[in] msgBufferSize Size of the message.
 * @param[in] status Status of the operation.
 * @param[in] reason Reason for job failure (if any).
 * @return uint32_t Size of the message.
 */
static uint32_t prvBuildStatusMessageSelfTest( char * pMsgBuffer,
                                               size_t msgBufferSize,
                                               OtaJobStatus_t status,
                                               int32_t reason );

/**
 * @brief Populate the response message with the status of the job.
 *
 * @param[in] pMsgBuffer Buffer to populate.
 * @param[in] msgBufferSize Size of the message.
 * @param[in] status Status of the operation.
 * @param[in] reason Reason for failure or the new firmware version.
 * @param[in] subReason Error code due to which the operation failed.
 * @param[in] previousVersion Version from which the new version was updated.
 * @return uint32_t Size of the message.
 */
static uint32_t prvBuildStatusMessageFinish( char * pMsgBuffer,
                                             size_t msgBufferSize,
                                             OtaJobStatus_t status,
                                             int32_t reason,
                                             int32_t subReason,
                                             uint32_t previousVersion );

/**
 * @brief Build a string from a set of strings
 *
 * @param[in] pBuffer Buffer to place the output string in.
 * @param[in] bufferSizeBytes Size of the buffer pointed to by pBuffer.
 * @param[in] strings NULL-terminated array of string pointers.
 * @return size_t Length of the output string, not including the terminator.
 */
static size_t stringBuilder( char * pBuffer,
                             size_t bufferSizeBytes,
                             const char * const strings[] );

/**
 * @brief Build a string with the decimal representation of a uint32_t value.
 *
 * @param[in] pBuffer Buffer to place the output string in.
 * @param[in] bufferSizeBytes Size of the buffer pointed to by pBuffer.
 * @param[in] value The uint32_t value to convert.
 * @return size_t Length of the output string, not including the terminator.
 */
static size_t stringBuilderUInt32Decimal( char * pBuffer,
                                          size_t bufferSizeBytes,
                                          uint32_t value );

/**
 * @brief Build a string with the hex representation of a uint32_t value.
 *
 * @param[in] pBuffer Buffer to place the output string in.
 * @param[in] bufferSizeBytes Size of the buffer pointed to by pBuffer.
 * @param[in] value The uint32_t value to convert.
 * @return size_t Length of the output string, not including the terminator.
 */
static size_t stringBuilderUInt32Hex( char * pBuffer,
                                      size_t bufferSizeBytes,
                                      uint32_t value );

static size_t stringBuilder( char * pBuffer,
                             size_t bufferSizeBytes,
                             const char * const strings[] )
{
    size_t curLen = 0;
    size_t i;
    size_t thisLength = 0;

    pBuffer[ 0 ] = '\0';

    for( i = 0; strings[ i ] != NULL; i++ )
    {
        thisLength = strlen( strings[ i ] );

        /* Assert if there is not enough buffer space. */

        assert( ( thisLength + curLen + 1U ) <= bufferSizeBytes );

        ( void ) strncat( pBuffer, strings[ i ], bufferSizeBytes - curLen - 1U );
        curLen += thisLength;
    }

    return curLen;
}

static size_t stringBuilderUInt32Decimal( char * pBuffer,
                                          size_t bufferSizeBytes,
                                          uint32_t value )
{
    char workBuf[ U32_MAX_LEN ];
    char * pCur = workBuf;
    char * pDest = pBuffer;
    uint32_t valueCopy = value;
    size_t size = 0;

    /* Assert if there is not enough buffer space. */

    assert( bufferSizeBytes >= U32_MAX_LEN );
    ( void ) bufferSizeBytes;

    while( valueCopy > 0U )
    {
        *pCur = asciiDigits[ ( valueCopy % 10U ) ];
        pCur++;
        valueCopy /= 10U;
    }

    while( pCur > workBuf )
    {
        pCur--;
        pDest[ size ] = *pCur;
        size++;
    }

    pDest[ size ] = '\0';
    size++;
    return size;
}

static size_t stringBuilderUInt32Hex( char * pBuffer,
                                      size_t bufferSizeBytes,
                                      uint32_t value )
{
    char workBuf[ U32_MAX_LEN ];
    char * pCur = workBuf;
    char * pDest = pBuffer;
    size_t size = 0;
    uint32_t valueCopy = value;
    size_t i;

    /* Assert if there is not enough buffer space. */

    assert( bufferSizeBytes >= U32_MAX_LEN );
    ( void ) bufferSizeBytes;

    /* Render all 8 digits, including leading zeros. */
    for( i = 0U; i < 8U; i++ )
    {
        *pCur = asciiDigits[ valueCopy & 15U ]; /* 15U = 0xF*/
        pCur++;
        valueCopy >>= 4;
    }

    while( pCur > workBuf )
    {
        pCur--;
        pDest[ size ] = *pCur;
        size++;
    }

    pDest[ size ] = '\0';
    size++;
    return size;
}

/*
 * Subscribe to the OTA job notification topics.
 */
static OtaMqttStatus_t subscribeToJobNotificationTopics( const OtaAgentContext_t * pAgentCtx )
{
    OtaMqttStatus_t mqttStatus = OtaMqttSuccess;

    uint16_t topicLen = 0;

    /* This buffer is used to store generated MQTT topics. The static size
     * are calculated from the templates and the corresponding parameters. */
    static char pJobTopicNotifyNext[ TOPIC_NOTIFY_NEXT_BUFFER_SIZE ];

    /* NULL-terminated list of topic string components */
    const char * topicStringParts[] =
    {
        MQTT_API_THINGS,
        NULL, /* Thing Name not available at compile time, initialized below */
        MQTT_API_JOBS_NOTIFY_NEXT,
        NULL
    };

    assert( pAgentCtx != NULL );

    /* Suppress warnings about unused variables. */
    ( void ) pOtaJobsNotifyNextTopicTemplate;

    topicStringParts[ 1 ] = ( const char * ) pAgentCtx->pThingName;

    topicLen = ( uint16_t ) stringBuilder(
        pJobTopicNotifyNext,
        sizeof( pJobTopicNotifyNext ),
        topicStringParts );

    /* The buffer is static and the size is calculated to fit. */
    assert( ( topicLen > 0U ) && ( topicLen < sizeof( pJobTopicNotifyNext ) ) );

    mqttStatus = pAgentCtx->pOtaInterface->mqtt.subscribe( pJobTopicNotifyNext,
                                                           topicLen,
                                                           1 );

    if( mqttStatus == OtaMqttSuccess )
    {
        LogInfo( ( "Subscribed to MQTT topic: %s", pJobTopicNotifyNext ) );
    }
    else
    {
        LogError( ( "Failed to subscribe to MQTT topic: "
                    "subscribe returned error: "
                    "OtaMqttStatus_t=%s"
                    ", topic=%s",
                    OTA_MQTT_strerror( mqttStatus ),
                    pJobTopicNotifyNext ) );
    }

    return mqttStatus;
}

/*
 * UnSubscribe from the OTA data stream topic.
 */
static OtaMqttStatus_t unsubscribeFromDataStream( const OtaAgentContext_t * pAgentCtx )
{
    OtaMqttStatus_t mqttStatus = OtaMqttSuccess;

    /* This buffer is used to store the generated MQTT topic. The static size
     * is calculated from the template and the corresponding parameters. */
    char pOtaRxStreamTopic[ TOPIC_STREAM_DATA_BUFFER_SIZE ];
    uint16_t topicLen = 0;
    const OtaFileContext_t * pFileContext = NULL;

    /* NULL-terminated list of topic string parts. */
    const char * topicStringParts[] =
    {
        MQTT_API_THINGS,
        NULL, /* Thing Name not available at compile time, initialized below. */
        MQTT_API_STREAMS,
        NULL, /* Stream Name not available at compile time, initialized below. */
        MQTT_API_DATA_CBOR,
        NULL
    };

    assert( pAgentCtx != NULL );

    pFileContext = &( pAgentCtx->fileContext );

    topicStringParts[ 1 ] = ( const char * ) pAgentCtx->pThingName;
    topicStringParts[ 3 ] = ( const char * ) pFileContext->pStreamName;

    /* Try to build the dynamic data stream topic and unsubscribe from it. */
    topicLen = ( uint16_t ) stringBuilder(
        pOtaRxStreamTopic,
        sizeof( pOtaRxStreamTopic ),
        topicStringParts );

    /* The buffer is static and the size is calculated to fit. */
    assert( ( topicLen > 0U ) && ( topicLen < sizeof( pOtaRxStreamTopic ) ) );

    mqttStatus = pAgentCtx->pOtaInterface->mqtt.unsubscribe( pOtaRxStreamTopic,
                                                             topicLen,
                                                             1 );

    if( mqttStatus == OtaMqttSuccess )
    {
        LogInfo( ( "Unsubscribed to MQTT topic: %s", pOtaRxStreamTopic ) );
    }
    else
    {
        LogError( ( "Failed to unsubscribe to MQTT topic: "
                    "unsubscribe returned error: "
                    "OtaMqttStatus_t=%s"
                    ", topic=%s",
                    OTA_MQTT_strerror( mqttStatus ),
                    pOtaRxStreamTopic ) );
    }

    return mqttStatus;
}

/*
 * Unsubscribe from the OTA job notification topics.
 */
static OtaMqttStatus_t unsubscribeFromJobNotificationTopic( const OtaAgentContext_t * pAgentCtx )
{
    OtaMqttStatus_t mqttStatus = OtaMqttSuccess;

    /* This buffer is used to store the generated MQTT topic. The static size
     * is calculated from the template and the corresponding parameters. This
     * buffer is used with two separate templates and its size is set fit the
     * larger of the two. */
    char pJobTopic[ TOPIC_NOTIFY_NEXT_BUFFER_SIZE ];
    uint16_t topicLen = 0;

    /* NULL-terminated list of topic string parts. */
    const char * topicStringParts[] =
    {
        MQTT_API_THINGS,
        NULL, /* Thing Name not available at compile time, initialized below. */
        MQTT_API_JOBS_NOTIFY_NEXT,
        NULL
    };

    assert( pAgentCtx != NULL );
    assert( pAgentCtx->pOtaInterface != NULL );
    assert( pAgentCtx->pOtaInterface->mqtt.unsubscribe != NULL );

    /* Try to unsubscribe from the first of two job topics. */

    topicStringParts[ 1 ] = ( const char * ) pAgentCtx->pThingName;
    topicLen = ( uint16_t ) stringBuilder(
        pJobTopic,
        sizeof( pJobTopic ),
        topicStringParts );

    /* The buffer is static and the size is calculated to fit. */
    assert( ( topicLen > 0U ) && ( topicLen < sizeof( pJobTopic ) ) );

    mqttStatus = pAgentCtx->pOtaInterface->mqtt.unsubscribe( pJobTopic,
                                                             topicLen,
                                                             0 );

    if( mqttStatus == OtaMqttSuccess )
    {
        LogInfo( ( "Unsubscribed to MQTT topic: %s", pJobTopic ) );
    }
    else
    {
        LogError( ( "Failed to unsubscribe to MQTT topic: "
                    "unsubscribe returned error: "
                    "OtaMqttStatus_t=%s"
                    ", topic=%s",
                    OTA_MQTT_strerror( mqttStatus ),
                    pJobTopic ) );
    }

    return mqttStatus;
}

/*
 * Publish a message to the job status topic.
 */
static OtaMqttStatus_t publishStatusMessage( const OtaAgentContext_t * pAgentCtx,
                                             const char * pMsg,
                                             uint32_t msgSize,
                                             uint8_t qos )
{
    OtaMqttStatus_t mqttStatus = OtaMqttSuccess;
    size_t topicLen = 0;

    /* This buffer is used to store the generated MQTT topic. The static size
     * is calculated from the template and the corresponding parameters. */
    char pTopicBuffer[ TOPIC_JOB_STATUS_BUFFER_SIZE ];
    /* NULL-terminated list of topic string parts. */
    const char * topicStringParts[] =
    {
        MQTT_API_THINGS,
        NULL, /* Thing Name not available at compile time, initialized below. */
        MQTT_API_JOBS,
        NULL, /* Active Job Name not available at compile time, initialized below. */
        MQTT_API_UPDATE,
        NULL
    };

    assert( pAgentCtx != NULL );
    /* pMsg is a static buffer of size "OTA_STATUS_MSG_MAX_SIZE". */
    assert( pMsg != NULL );

    /* Suppress warnings about unused variables. */
    ( void ) pOtaJobStatusTopicTemplate;

    /* Build the dynamic job status topic . */

    topicStringParts[ 1 ] = ( const char * ) pAgentCtx->pThingName;
    topicStringParts[ 3 ] = ( const char * ) pAgentCtx->pActiveJobName;

    topicLen = stringBuilder(
        pTopicBuffer,
        sizeof( pTopicBuffer ),
        topicStringParts );

    /* The buffer is static and the size is calculated to fit. */
    assert( ( topicLen > 0U ) && ( topicLen < sizeof( pTopicBuffer ) ) );

    /* Publish the status message. */
    LogDebug( ( "Attempting to publish MQTT status message: "
                "message=%s",
                pMsg ) );

    mqttStatus = pAgentCtx->pOtaInterface->mqtt.publish( pTopicBuffer,
                                                         ( uint16_t ) topicLen,
                                                         &pMsg[ 0 ],
                                                         msgSize,
                                                         qos );

    if( mqttStatus == OtaMqttSuccess )
    {
        LogDebug( ( "Published to MQTT topic: "
                    "topic=%s",
                    pTopicBuffer ) );
    }
    else
    {
        LogError( ( "Failed to publish MQTT message: "
                    "publish returned error: "
                    "OtaMqttStatus_t=%s"
                    ", topic=%s",
                    OTA_MQTT_strerror( mqttStatus ),
                    pTopicBuffer ) );
    }

    return mqttStatus;
}

static uint32_t buildStatusMessageReceiving( char * pMsgBuffer,
                                             size_t msgBufferSize,
                                             OtaJobStatus_t status,
                                             const OtaFileContext_t * pOTAFileCtx )
{
    char receivedString[ U32_MAX_LEN + 1 ];
    char numBlocksString[ U32_MAX_LEN + 1 ];
    uint32_t numBlocks = 0;
    uint32_t received = 0;
    uint32_t msgSize = 0;
    /* NULL-terminated list of JSON payload components */
    /* NOTE: this must conform to the following format, do not add spaces, etc. */
    /*       "\"%s\":\"%u/%u\"}}" */

    const char * payloadStringParts[] =
    {
        NULL, /* Job status is not available at compile time, initialized below. */
        pOtaStringReceive,
        ":\"",
        NULL, /* Received string is not available at compile time, initialized below. */
        "/",
        NULL, /* # blocks string is not available at compile time, initialized below. */
        "\"}}",
        NULL
    };

    assert( pMsgBuffer != NULL );
    /* This function is only called when a file is received, so it can't be NULL. */
    assert( pOTAFileCtx != NULL );

    numBlocks = ( pOTAFileCtx->fileSize + ( OTA_FILE_BLOCK_SIZE - 1U ) ) >> otaconfigLOG2_FILE_BLOCK_SIZE;
    received = numBlocks - pOTAFileCtx->blocksRemaining;

    /* Output a status update when receiving first file block to let user know the OTA job status
     * more clearly. Then output a status update once in a while. */

    if( ( received == 1U ) || ( ( received % ( uint32_t ) otaconfigOTA_UPDATE_STATUS_FREQUENCY ) == 0U ) )
    {
        payloadStringParts[ 0 ] = pOtaJobStatusStrings[ status ];
        payloadStringParts[ 3 ] = receivedString;
        payloadStringParts[ 5 ] = numBlocksString;

        ( void ) stringBuilderUInt32Decimal( receivedString, sizeof( receivedString ), received );
        ( void ) stringBuilderUInt32Decimal( numBlocksString, sizeof( numBlocksString ), numBlocks );


        msgSize = ( uint32_t ) stringBuilder(
            pMsgBuffer,
            msgBufferSize,
            payloadStringParts );

        /* The buffer is static and the size is calculated to fit. */
        assert( ( msgSize > 0U ) && ( msgSize < msgBufferSize ) );
    }

    return msgSize;
}

static uint32_t prvBuildStatusMessageSelfTest( char * pMsgBuffer,
                                               size_t msgBufferSize,
                                               OtaJobStatus_t status,
                                               int32_t reason )
{
    uint32_t msgSize = 0;

    /* NULL-terminated list of JSON payload components */
    /* NOTE: this must agree with the following format, do not add spaces, etc. */
    /*       "\"%s\":\"%s\",\"" OTA_JSON_UPDATED_BY_KEY_ONLY "\":\"0x%x\"}}" */
    char versionString[ U32_MAX_LEN + 1 ];
    const char * pPayloadStringParts[] =
    {
        NULL, /* Job status string not available at compile time, initialized below. */
        "\"",
        OTA_JSON_SELF_TEST_KEY_ONLY,
        "\":\"",
        NULL, /* Job reason string not available at compile time, initialized below. */
        "\",\"" OTA_JSON_UPDATED_BY_KEY_ONLY "\":\"0x",
        NULL, /* Version string not available at compile time, initialized below. */
        "\"}}",
        NULL
    };

    assert( pMsgBuffer != NULL );

    ( void ) stringBuilderUInt32Hex( versionString, sizeof( versionString ), appFirmwareVersion.u.unsignedVersion32 );
    pPayloadStringParts[ 0 ] = pOtaJobStatusStrings[ status ];
    pPayloadStringParts[ 4 ] = pOtaJobReasonStrings[ reason ];
    pPayloadStringParts[ 6 ] = versionString;

    msgSize = ( uint32_t ) stringBuilder(
        pMsgBuffer,
        msgBufferSize,
        pPayloadStringParts );

    assert( ( msgSize > 0U ) && ( msgSize < msgBufferSize ) );

    LogDebug( ( "Created self test update: %s", pMsgBuffer ) );

    return msgSize;
}

static uint32_t prvBuildStatusMessageFinish( char * pMsgBuffer,
                                             size_t msgBufferSize,
                                             OtaJobStatus_t status,
                                             int32_t reason,
                                             int32_t subReason,
                                             uint32_t previousVersion )
{
    uint32_t msgSize = 0;
    char reasonString[ U32_MAX_LEN + 1 ];
    char subReasonString[ U32_MAX_LEN + 1 ];
    char newVersionMajorString[ U32_MAX_LEN + 1 ];
    char newVersionMinorString[ U32_MAX_LEN + 1 ];
    char newVersionBuildString[ U32_MAX_LEN + 1 ];
    char prevVersionMajorString[ U32_MAX_LEN + 1 ];
    char prevVersionMinorString[ U32_MAX_LEN + 1 ];
    char prevVersionBuildString[ U32_MAX_LEN + 1 ];

    AppVersion32_t newVersion = { 0 }, prevVersion = { 0 };

    /* NULL-terminated list of payload string parts */
    /* NOTE: this must conform to the following format, do not add spaces, etc. */
    /*       "\"reason\":\"0x%08x: 0x%08x\"}}" */

    const char * pPayloadPartsStatusFailedWithValue[] =
    {
        NULL, /* Job status string not available at compile time, initialized below. */
        "\"reason\":\"0x",
        NULL, /* Reason string not available at compile time, initialized below. */
        ": 0x",
        NULL, /* Sub-Reason string not available at compile time, initialized below. */
        "\"}}",
        NULL
    };
    /* NULL-terminated list of payload string parts */
    /* NOTE: this must agree with the following format, do not add spaces, etc. */
    /*       "\"reason\":\"%s v%u.%u.%u\"}}" */
    const char * pPayloadPartsStatusSucceeded[] =
    {
        NULL,                                         /* Job status string not available at compile time, initialized below. */
        "\"reason\":\"",
        NULL,                                         /*  Reason string not available at compile time, initialized below. */
        "  v",
        NULL,                                         /* Version major string not available at compile time, initialized below. */
        ".",
        NULL,                                         /* Version minor string not available at compile time, initialized below. */
        ".",
        NULL,                                         /* Version build string not available at compile time, initialized below. */
        "\",\"" OTA_JSON_UPDATED_BY_KEY_ONLY "\":\"", /* Expands to `","updatedBy":` */
        "  v",
        NULL,                                         /* Previous version major string not available at compile time, initialized below. */
        ".",
        NULL,                                         /* Previous version minor string not available at compile time, initialized below. */
        ".",
        NULL,                                         /* Previous version build string not available at compile time, initialized below. */
        "\"}}",
        NULL
    };

    /* NULL-terminated list of payload string parts */
    /* NOTE: this must agree with the following format, do not add spaces, etc. */
    /*       "\"reason\":\"%s: 0x%08x\"}}" */
    const char * pPayloadPartsStatusOther[] =
    {
        NULL, /* Job status string not available at compile time, initialized below. */
        "\"reason\":\"",
        NULL, /*  Reason string not available at compile time, initialized below. */
        ": 0x",
        NULL, /* Sub-Reason string not available at compile time, initialized below. */
        "\"}}",
        NULL
    };
    const char ** pPayloadParts;

    assert( pMsgBuffer != NULL );

    newVersion.u.signedVersion32 = subReason;
    prevVersion.u.signedVersion32 = ( int32_t ) previousVersion;

    ( void ) stringBuilderUInt32Hex( reasonString, sizeof( reasonString ), ( uint32_t ) reason );
    ( void ) stringBuilderUInt32Hex( subReasonString, sizeof( subReasonString ), ( uint32_t ) subReason );

    /* FailedWithVal uses a numeric OTA error code and sub-reason code to cover
     * the case where there may be too many description strings to reasonably
     * include in the code.
     */
    if( status == JobStatusFailedWithVal )
    {
        pPayloadParts = pPayloadPartsStatusFailedWithValue;
        pPayloadParts[ 0 ] = pOtaJobStatusStrings[ status ];
        pPayloadParts[ 2 ] = reasonString;
        pPayloadParts[ 4 ] = subReasonString;
    }

    /* If the status update is for "Succeeded," we are identifying the version
     * of firmware that has been accepted. This makes it easy to find the
     * version associated with each device (Thing) when examining the OTA jobs
     * on the service side via the CLI or possibly with some console tool.
     */
    else if( status == JobStatusSucceeded )
    {
        /* New version string.*/
        ( void ) stringBuilderUInt32Decimal( newVersionMajorString, sizeof( newVersionMajorString ), newVersion.u.x.major );
        ( void ) stringBuilderUInt32Decimal( newVersionMinorString, sizeof( newVersionMinorString ), newVersion.u.x.minor );
        ( void ) stringBuilderUInt32Decimal( newVersionBuildString, sizeof( newVersionBuildString ), newVersion.u.x.build );

        /* Updater version string.*/
        ( void ) stringBuilderUInt32Decimal( prevVersionMajorString, sizeof( prevVersionMajorString ), prevVersion.u.x.major );
        ( void ) stringBuilderUInt32Decimal( prevVersionMinorString, sizeof( prevVersionMinorString ), prevVersion.u.x.minor );
        ( void ) stringBuilderUInt32Decimal( prevVersionBuildString, sizeof( prevVersionMinorString ), prevVersion.u.x.build );

        pPayloadParts = pPayloadPartsStatusSucceeded;
        pPayloadParts[ 0 ] = pOtaJobStatusStrings[ status ];
        pPayloadParts[ 2 ] = pOtaJobReasonStrings[ reason ];
        pPayloadParts[ 4 ] = newVersionMajorString;
        pPayloadParts[ 6 ] = newVersionMinorString;
        pPayloadParts[ 8 ] = newVersionBuildString;
        pPayloadParts[ 11 ] = prevVersionMajorString;
        pPayloadParts[ 13 ] = prevVersionMinorString;
        pPayloadParts[ 15 ] = prevVersionBuildString;
    }
    else
    {
        pPayloadParts = pPayloadPartsStatusOther;
        pPayloadParts[ 0 ] = pOtaJobStatusStrings[ status ];
        pPayloadParts[ 2 ] = pOtaJobReasonStrings[ reason ];
        pPayloadParts[ 4 ] = subReasonString;
    }

    msgSize = ( uint32_t ) stringBuilder(
        pMsgBuffer,
        msgBufferSize,
        pPayloadParts );

    /* The buffer is static and the size is calculated to fit. */
    assert( ( msgSize > 0U ) && ( msgSize < msgBufferSize ) );

    return msgSize;
}

/*
 * Check for next available OTA job from the job service by publishing
 * a "get next job" message to the job service.
 */

OtaErr_t requestJob_Mqtt( const OtaAgentContext_t * pAgentCtx )
{
    /* This buffer is used to store the generated MQTT topic. The static size
     * is calculated from the template and the corresponding parameters. */
    char pJobTopic[ TOPIC_GET_NEXT_BUFFER_SIZE ];

    /* The following buffer is big enough to hold a dynamically constructed
     * $next/get job message. It contains a client token that is used to track
     * how many requests have been made. */
    char pMsg[ MSG_GET_NEXT_BUFFER_SIZE ];

    static uint32_t reqCounter = 0;
    OtaErr_t otaError = OtaErrRequestJobFailed;
    OtaMqttStatus_t mqttStatus = OtaMqttSuccess;
    uint32_t msgSize = 0;
    uint16_t topicLen = 0;

    /* NULL-terminated list of topic string parts. */
    const char * pTopicParts[] =
    {
        MQTT_API_THINGS,
        NULL, /* Thing Name not available at compile time, initialized below. */
        MQTT_API_JOBS_NEXT_GET,
        NULL
    };
    char reqCounterString[ U32_MAX_LEN + 1 ];
    /* NULL-terminated list of payload parts */
    /* NOTE: this must agree with pOtaGetNextJobMsgTemplate, do not add spaces, etc. */
    const char * pPayloadParts[] =
    {
        "{\"clientToken\":\"",
        NULL, /* Request counter string not available at compile time, initialized below. */
        ":",
        NULL, /* Thing Name not available at compile time, initialized below. */
        "\"}",
        NULL
    };

    assert( pAgentCtx != NULL );

    /* Suppress warnings about unused variables. */
    ( void ) pOtaJobsGetNextTopicTemplate;
    ( void ) pOtaGetNextJobMsgTemplate;

    pTopicParts[ 1 ] = ( const char * ) pAgentCtx->pThingName;
    pPayloadParts[ 1 ] = reqCounterString;
    pPayloadParts[ 3 ] = ( const char * ) pAgentCtx->pThingName;

    ( void ) stringBuilderUInt32Decimal( reqCounterString, sizeof( reqCounterString ), reqCounter );

    /* Subscribe to the OTA job notification topic. */
    mqttStatus = subscribeToJobNotificationTopics( pAgentCtx );

    if( mqttStatus == OtaMqttSuccess )
    {
        LogDebug( ( "MQTT job request number: counter=%u", reqCounter ) );

        msgSize = ( uint32_t ) stringBuilder(
            pMsg,
            sizeof( pMsg ),
            pPayloadParts );

        /* The buffer is static and the size is calculated to fit. */
        assert( ( msgSize > 0U ) && ( msgSize < sizeof( pMsg ) ) );

        reqCounter++;

        topicLen = ( uint16_t ) stringBuilder(
            pJobTopic,
            sizeof( pJobTopic ),
            pTopicParts );

        /* The buffer is static and the size is calculated to fit. */
        assert( ( topicLen > 0U ) && ( topicLen < sizeof( pJobTopic ) ) );

        mqttStatus = pAgentCtx->pOtaInterface->mqtt.publish( pJobTopic, topicLen, pMsg, msgSize, 1 );

        if( mqttStatus == OtaMqttSuccess )
        {
            LogDebug( ( "Published MQTT request to get the next job: "
                        "topic=%s",
                        pJobTopic ) );
            otaError = OtaErrNone;
        }
        else
        {
            LogError( ( "Failed to publish MQTT message:"
                        "publish returned error: "
                        "OtaMqttStatus_t=%s",
                        OTA_MQTT_strerror( mqttStatus ) ) );
        }
    }

    return otaError;
}


/*
 * Update the job status on the service side with progress or completion info.
 */
OtaErr_t updateJobStatus_Mqtt( const OtaAgentContext_t * pAgentCtx,
                               OtaJobStatus_t status,
                               int32_t reason,
                               int32_t subReason )
{
    OtaErr_t result = OtaErrNone;
    OtaMqttStatus_t mqttStatus = OtaMqttPublishFailed;
    /* A message size of zero means don't publish anything. */
    uint32_t msgSize = 0U;
    /* All job state transitions except streaming progress use QOS 1 since it is required to have status in the job document. */
    char pMsg[ OTA_STATUS_MSG_MAX_SIZE ];
    uint8_t qos = 1;
    const OtaFileContext_t * pFileContext = NULL;

    assert( pAgentCtx != NULL );

    /* Get the current file context. */
    pFileContext = &( pAgentCtx->fileContext );

    if( status == JobStatusInProgress )
    {
        if( reason == ( int32_t ) JobReasonReceiving )
        {
            msgSize = buildStatusMessageReceiving( pMsg, sizeof( pMsg ), status, pFileContext );

            /* Downgrade Progress updates to QOS 0 to avoid overloading MQTT buffers during active streaming. */
            qos = 0;
        }
        else
        {
            /* We're no longer receiving but we're still In Progress so we are implicitly in the Self
             * Test phase. Prepare to update the job status with the self_test phase (ready or active). */
            msgSize = prvBuildStatusMessageSelfTest( pMsg, sizeof( pMsg ), status, reason );
        }
    }
    else
    {
        /* The potential values for status are constant at compile time. */
        assert( status < NumJobStatusMappings );
        msgSize = prvBuildStatusMessageFinish( pMsg, sizeof( pMsg ), status, reason, subReason, pAgentCtx->fileContext.updaterVersion );
    }

    if( msgSize > 0U )
    {
        /* Publish the string created above. */
        mqttStatus = publishStatusMessage( pAgentCtx, pMsg, msgSize, qos );

        if( mqttStatus == OtaMqttSuccess )
        {
            LogDebug( ( "Published update to the job status." ) );
        }
        else
        {
            LogError( ( "Failed to publish MQTT status message: "
                        "publishStatusMessage returned error: "
                        "OtaMqttStatus_t=%s",
                        OTA_MQTT_strerror( mqttStatus ) ) );

            result = OtaErrUpdateJobStatusFailed;
        }
    }

    return result;
}

/*
 * Init file transfer by subscribing to the OTA data stream topic.
 */
OtaErr_t initFileTransfer_Mqtt( const OtaAgentContext_t * pAgentCtx )
{
    OtaErr_t result = OtaErrInitFileTransferFailed;
    OtaMqttStatus_t mqttStatus = OtaMqttSuccess;

    /* This buffer is used to store the generated MQTT topic. The static size
     * is calculated from the template and the corresponding parameters. */
    static char pRxStreamTopic[ TOPIC_STREAM_DATA_BUFFER_SIZE ]; /*!< Buffer to store the topic generated for requesting data stream. */
    uint16_t topicLen = 0;
    const OtaFileContext_t * pFileContext = NULL;

    /* NULL-terminated list of topic string parts. */
    const char * pTopicParts[] =
    {
        MQTT_API_THINGS,
        NULL, /* Thing Name not available at compile time, initialized below. */
        MQTT_API_STREAMS,
        NULL, /* Stream Name not available at compile time, initialized below. */
        MQTT_API_DATA_CBOR,
        NULL
    };

    assert( pAgentCtx != NULL );

    /* Suppress warnings about unused variables. */
    ( void ) pOtaStreamDataTopicTemplate;

    pFileContext = &( pAgentCtx->fileContext );
    pTopicParts[ 1 ] = ( const char * ) pAgentCtx->pThingName;
    pTopicParts[ 3 ] = ( const char * ) pFileContext->pStreamName;

    topicLen = ( uint16_t ) stringBuilder(
        pRxStreamTopic,
        sizeof( pRxStreamTopic ),
        pTopicParts );

    /* The buffer is static and the size is calculated to fit. */
    assert( ( topicLen > 0U ) && ( topicLen < sizeof( pRxStreamTopic ) ) );

    mqttStatus = pAgentCtx->pOtaInterface->mqtt.subscribe( pRxStreamTopic,
                                                           topicLen,
                                                           0 );

    if( mqttStatus == OtaMqttSuccess )
    {
        LogDebug( ( "Subscribed to the OTA data stream topic: "
                    "topic=%s",
                    pRxStreamTopic ) );
        result = OtaErrNone;
    }
    else
    {
        LogError( ( "Failed to subscribe to MQTT topic: "
                    "subscribe returned error: "
                    "OtaMqttStatus_t=%s"
                    ", topic=%s",
                    OTA_MQTT_strerror( mqttStatus ),
                    pRxStreamTopic ) );
    }

    return result;
}

/*
 * Request file block by publishing to the get stream topic.
 */
OtaErr_t requestFileBlock_Mqtt( OtaAgentContext_t * pAgentCtx )
{
    OtaErr_t result = OtaErrRequestFileBlockFailed;
    OtaMqttStatus_t mqttStatus = OtaMqttSuccess;
    size_t msgSizeFromStream = 0;
    uint32_t blockSize = OTA_FILE_BLOCK_SIZE;
    uint32_t numBlocks = 0;
    uint32_t bitmapLen = 0;
    uint32_t msgSizeToPublish = 0;
    uint32_t topicLen = 0;
    bool cborEncodeRet = false;
    char pMsg[ OTA_REQUEST_MSG_MAX_SIZE ];

    /* This buffer is used to store the generated MQTT topic. The static size
     * is calculated from the template and the corresponding parameters. */
    char pTopicBuffer[ TOPIC_GET_STREAM_BUFFER_SIZE ];
    const OtaFileContext_t * pFileContext = NULL;

    /* NULL-terminated list of topic string parts. */
    const char * pTopicParts[] =
    {
        MQTT_API_THINGS,
        NULL, /* Thing Name not available at compile time, initialized below. */
        MQTT_API_STREAMS,
        NULL, /* Stream Name not available at compile time, initialized below. */
        MQTT_API_GET_CBOR,
        NULL
    };

    assert( pAgentCtx != NULL );

    /* Suppress warnings about unused variables. */
    ( void ) pOtaGetStreamTopicTemplate;

    /* Get the current file context. */
    pFileContext = &( pAgentCtx->fileContext );

    pTopicParts[ 1 ] = ( const char * ) pAgentCtx->pThingName;
    pTopicParts[ 3 ] = ( const char * ) pFileContext->pStreamName;

    /* Reset number of blocks requested. */
    pAgentCtx->numOfBlocksToReceive = otaconfigMAX_NUM_BLOCKS_REQUEST;

    numBlocks = ( pFileContext->fileSize + ( OTA_FILE_BLOCK_SIZE - 1U ) ) >> otaconfigLOG2_FILE_BLOCK_SIZE;
    bitmapLen = ( numBlocks + ( BITS_PER_BYTE - 1U ) ) >> LOG2_BITS_PER_BYTE;

    cborEncodeRet = OTA_CBOR_Encode_GetStreamRequestMessage( ( uint8_t * ) pMsg,
                                                             sizeof( pMsg ),
                                                             &msgSizeFromStream,
                                                             OTA_CLIENT_TOKEN,
                                                             ( int32_t ) pFileContext->serverFileID,
                                                             ( int32_t ) blockSize,
                                                             0,
                                                             pFileContext->pRxBlockBitmap,
                                                             bitmapLen,
                                                             ( int32_t ) otaconfigMAX_NUM_BLOCKS_REQUEST );

    if( cborEncodeRet == true )
    {
        msgSizeToPublish = ( uint32_t ) msgSizeFromStream;

        /* Try to build the dynamic data REQUEST topic to publish to. */

        topicLen = ( uint32_t ) stringBuilder(
            pTopicBuffer,
            sizeof( pTopicBuffer ),
            pTopicParts );

        /* The buffer is static and the size is calculated to fit. */
        assert( ( topicLen > 0U ) && ( topicLen < sizeof( pTopicBuffer ) ) );

        mqttStatus = pAgentCtx->pOtaInterface->mqtt.publish( pTopicBuffer,
                                                             ( uint16_t ) topicLen,
                                                             &pMsg[ 0 ],
                                                             msgSizeToPublish,
                                                             0 );

        if( mqttStatus == OtaMqttSuccess )
        {
            LogInfo( ( "Published to MQTT topic to request the next block: "
                       "topic=%s",
                       pTopicBuffer ) );
            result = OtaErrNone;
        }
        else
        {
            LogError( ( "Failed to publish MQTT message: "
                        "publish returned error: "
                        "OtaMqttStatus_t=%s",
                        OTA_MQTT_strerror( mqttStatus ) ) );
        }
    }
    else
    {
        result = OtaErrFailedToEncodeCbor;
        LogError( ( "Failed to CBOR encode stream request message: "
                    "OTA_CBOR_Encode_GetStreamRequestMessage returned error." ) );
    }

    return result;
}

/*
 * Decode a cbor encoded fileblock received from streaming service.
 */
OtaErr_t decodeFileBlock_Mqtt( const uint8_t * pMessageBuffer,
                               size_t messageSize,
                               int32_t * pFileId,
                               int32_t * pBlockId,
                               int32_t * pBlockSize,
                               uint8_t * const * pPayload,
                               size_t * pPayloadSize )
{
    OtaErr_t result = OtaErrFailedToDecodeCbor;
    bool cborDecodeRet = false;

    /* Decode the CBOR content. */
    cborDecodeRet = OTA_CBOR_Decode_GetStreamResponseMessage( pMessageBuffer,
                                                              messageSize,
                                                              pFileId,
                                                              pBlockId,   /* CBOR requires pointer to int and our block indices never exceed 31 bits. */
                                                              pBlockSize, /* CBOR requires pointer to int and our block sizes never exceed 31 bits. */
                                                              pPayload,   /* This payload gets malloc'd by OTA_CBOR_Decode_GetStreamResponseMessage(). We must free it. */
                                                              pPayloadSize );

    if( cborDecodeRet == true )
    {
        /* pPayload and pPayloadSize is allocated by the caller. */
        assert( ( pPayload != NULL ) && ( pPayloadSize != NULL ) );

        result = OtaErrNone;
    }
    else
    {
        LogError( ( "Failed to decode MQTT file block: "
                    "OTA_CBOR_Decode_GetStreamResponseMessage returned error." ) );
    }

    return result;
}

/*
 * Perform any cleanup operations required for control plane.
 */
OtaErr_t cleanupControl_Mqtt( const OtaAgentContext_t * pAgentCtx )
{
    OtaErr_t result = OtaErrNone;
    OtaMqttStatus_t mqttStatus = OtaMqttSuccess;

    assert( pAgentCtx != NULL );

    if( pAgentCtx->unsubscribeOnShutdown != 0U )
    {
        /* Unsubscribe from job notification topics. */
        mqttStatus = unsubscribeFromJobNotificationTopic( pAgentCtx );

        if( mqttStatus != OtaMqttSuccess )
        {
            LogWarn( ( "Failed cleanup for MQTT control plane: "
                       "unsubscribeFromJobNotificationTopic returned error: "
                       "OtaMqttStatus_t=%s",
                       OTA_MQTT_strerror( mqttStatus ) ) );
            result = OtaErrCleanupControlFailed;
        }
    }

    return result;
}

/*
 * Perform any cleanup operations required for data plane.
 */
OtaErr_t cleanupData_Mqtt( const OtaAgentContext_t * pAgentCtx )
{
    OtaErr_t result = OtaErrNone;
    OtaMqttStatus_t mqttStatus = OtaMqttSuccess;

    assert( pAgentCtx != NULL );

    if( pAgentCtx->unsubscribeOnShutdown != 0U )
    {
        /* Unsubscribe from data stream topics. */
        mqttStatus = unsubscribeFromDataStream( pAgentCtx );

        if( mqttStatus != OtaMqttSuccess )
        {
            LogWarn( ( "Failed cleanup for MQTT data plane: "
                       "unsubscribeFromDataStream returned error: "
                       "OtaMqttStatus_t=%s",
                       OTA_MQTT_strerror( mqttStatus ) ) );
            result = OtaErrCleanupDataFailed;
        }
    }

    return result;
}

const char * OTA_MQTT_strerror( OtaMqttStatus_t status )
{
    const char * str = NULL;

    switch( status )
    {
        case OtaMqttSuccess:
            str = "OtaMqttSuccess";
            break;

        case OtaMqttPublishFailed:
            str = "OtaMqttPublishFailed";
            break;

        case OtaMqttSubscribeFailed:
            str = "OtaMqttSubscribeFailed";
            break;

        case OtaMqttUnsubscribeFailed:
            str = "OtaMqttUnsubscribeFailed";
            break;

        default:
            str = "InvalidErrorCode";
            break;
    }

    return str;
}
