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
 * @file ota_utest.c
 * @brief Unit tests for functions in OTA agent.
 */

/* Standard includes. */
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>
#include <stdint.h>

/* 3rdparty includes. */
#include <unistd.h>
#include "unity.h"

/* OTA includes. */
#include "ota_appversion32.h"
#include "ota.h"
#include "ota_private.h"
#include "ota_mqtt_private.h"
#include "ota_http_private.h"
#include "ota_interface_private.h"

/* test includes. */
#include "utest_helpers.h"

/* Job document for testing. */
#define OTA_FILE_SIZE_OVERFLOW            "4294963220"
#define OTA_TEST_FILE_SIZE                10240
#define OTA_TEST_FILE_NUM_BLOCKS          ( OTA_TEST_FILE_SIZE / OTA_FILE_BLOCK_SIZE + 1 )
#define OTA_TEST_DUPLICATE_NUM_BLOCKS     3
#define OTA_TEST_FILE_SIZE_STR            "10240"
#define JOB_DOC_A                         "{\"clientToken\":\"0:testclient\",\"timestamp\":1602795143,\"execution\":{\"jobId\":\"AFR_OTA-testjob20\",\"status\":\"QUEUED\",\"queuedAt\":1602795128,\"lastUpdatedAt\":1602795128,\"versionNumber\":1,\"executionNumber\":1,\"jobDocument\":{\"afr_ota\":{\"protocols\":[\"MQTT\"],\"streamname\":\"AFR_OTA-XYZ\",\"files\":[{\"filepath\":\"/test/demo\",\"filesize\":" OTA_TEST_FILE_SIZE_STR ",\"fileid\":0,\"certfile\":\"test.crt\",\"sig-sha256-ecdsa\":\"MEQCIF2QDvww1G/kpRGZ8FYvQrok1bSZvXjXefRk7sqNcyPTAiB4dvGt8fozIY5NC0vUDJ2MY42ZERYEcrbwA4n6q7vrBg==\"}] }}}}"
#define JOB_DOC_B                         "{\"clientToken\":\"0:testclient\",\"timestamp\":1602795143,\"execution\":{\"jobId\":\"AFR_OTA-testjob21\",\"status\":\"QUEUED\",\"queuedAt\":1602795128,\"lastUpdatedAt\":1602795128,\"versionNumber\":1,\"executionNumber\":1,\"jobDocument\":{\"afr_ota\":{\"protocols\":[\"MQTT\"],\"streamname\":\"AFR_OTA-XYZ\",\"files\":[{\"filepath\":\"/test/demo\",\"filesize\":" OTA_TEST_FILE_SIZE_STR ",\"fileid\":0,\"certfile\":\"test.crt\",\"sig-sha256-ecdsa\":\"MEQCIF2QDvww1G/kpRGZ8FYvQrok1bSZvXjXefRk7sqNcyPTAiB4dvGt8fozIY5NC0vUDJ2MY42ZERYEcrbwA4n6q7vrBg==\"}] }}}}"
#define JOB_DOC_SELF_TEST                 "{\"clientToken\":\"0:testclient\",\"timestamp\":1602795143,\"execution\":{\"jobId\":\"AFR_OTA-testjob20\",\"status\":\"IN_PROGRESS\",\"statusDetails\":{\"self_test\":\"ready\",\"updatedBy\":\"0x1000000\"},\"queuedAt\":1602795128,\"lastUpdatedAt\":1602795128,\"versionNumber\":1,\"executionNumber\":1,\"jobDocument\":{\"afr_ota\":{\"protocols\":[\"MQTT\"],\"streamname\":\"AFR_OTA-XYZ\",\"files\":[{\"filepath\":\"/test/demo\",\"filesize\":" OTA_TEST_FILE_SIZE_STR ",\"fileid\":0,\"certfile\":\"test.crt\",\"sig-sha256-ecdsa\":\"MEQCIF2QDvww1G/kpRGZ8FYvQrok1bSZvXjXefRk7sqNcyPTAiB4dvGt8fozIY5NC0vUDJ2MY42ZERYEcrbwA4n6q7vrBg==\"}] }}}}"
#define JOB_DOC_SELF_TEST_FILE_TYPE       "{\"clientToken\":\"0:testclient\",\"timestamp\":1602795143,\"execution\":{\"jobId\":\"AFR_OTA-testjob20\",\"status\":\"IN_PROGRESS\",\"statusDetails\":{\"self_test\":\"ready\",\"updatedBy\":\"0x1000000\"},\"queuedAt\":1602795128,\"lastUpdatedAt\":1602795128,\"versionNumber\":1,\"executionNumber\":1,\"jobDocument\":{\"afr_ota\":{\"protocols\":[\"MQTT\"],\"streamname\":\"AFR_OTA-XYZ\",\"files\":[{\"filepath\":\"/test/demo\",\"filesize\":" OTA_TEST_FILE_SIZE_STR ",\"fileid\":0,\"certfile\":\"test.crt\",\"fileType\":255,\"sig-sha256-ecdsa\":\"MEQCIF2QDvww1G/kpRGZ8FYvQrok1bSZvXjXefRk7sqNcyPTAiB4dvGt8fozIY5NC0vUDJ2MY42ZERYEcrbwA4n6q7vrBg==\"}] }}}}"
#define JOB_DOC_SELF_TEST_SAME_VERSION    "{\"clientToken\":\"0:testclient\",\"timestamp\":1602795143,\"execution\":{\"jobId\":\"AFR_OTA-testjob20\",\"status\":\"IN_PROGRESS\",\"statusDetails\":{\"self_test\":\"ready\",\"updatedBy\":\"0x1000001\"},\"queuedAt\":1602795128,\"lastUpdatedAt\":1602795128,\"versionNumber\":1,\"executionNumber\":1,\"jobDocument\":{\"afr_ota\":{\"protocols\":[\"MQTT\"],\"streamname\":\"AFR_OTA-XYZ\",\"files\":[{\"filepath\":\"/test/demo\",\"filesize\":" OTA_TEST_FILE_SIZE_STR ",\"fileid\":0,\"certfile\":\"test.crt\",\"sig-sha256-ecdsa\":\"MEQCIF2QDvww1G/kpRGZ8FYvQrok1bSZvXjXefRk7sqNcyPTAiB4dvGt8fozIY5NC0vUDJ2MY42ZERYEcrbwA4n6q7vrBg==\"}] }}}}"
#define JOB_DOC_SELF_TEST_DOWNGRADE       "{\"clientToken\":\"0:testclient\",\"timestamp\":1602795143,\"execution\":{\"jobId\":\"AFR_OTA-testjob20\",\"status\":\"IN_PROGRESS\",\"statusDetails\":{\"self_test\":\"ready\",\"updatedBy\":\"0x2000000\"},\"queuedAt\":1602795128,\"lastUpdatedAt\":1602795128,\"versionNumber\":1,\"executionNumber\":1,\"jobDocument\":{\"afr_ota\":{\"protocols\":[\"MQTT\"],\"streamname\":\"AFR_OTA-XYZ\",\"files\":[{\"filepath\":\"/test/demo\",\"filesize\":" OTA_TEST_FILE_SIZE_STR ",\"fileid\":0,\"certfile\":\"test.crt\",\"sig-sha256-ecdsa\":\"MEQCIF2QDvww1G/kpRGZ8FYvQrok1bSZvXjXefRk7sqNcyPTAiB4dvGt8fozIY5NC0vUDJ2MY42ZERYEcrbwA4n6q7vrBg==\"}] }}}}"
#define JOB_DOC_HTTP                      "{\"clientToken\":\"0:testclient\",\"timestamp\":1602795143,\"execution\":{\"jobId\":\"AFR_OTA-testjob22\",\"status\":\"QUEUED\",\"queuedAt\":1602795128,\"lastUpdatedAt\":1602795128,\"versionNumber\":1,\"executionNumber\":1,\"jobDocument\":{\"afr_ota\":{\"protocols\":[\"HTTP\"],\"files\":[{\"filepath\":\"/test/demo\",\"filesize\":" OTA_TEST_FILE_SIZE_STR ",\"fileid\":0,\"certfile\":\"test.crt\",\"update_data_url\":\"https://dummy-url.com/ota.bin\",\"auth_scheme\":\"aws.s3.presigned\",\"sig-sha256-ecdsa\":\"MEQCIF2QDvww1G/kpRGZ8FYvQrok1bSZvXjXefRk7sqNcyPTAiB4dvGt8fozIY5NC0vUDJ2MY42ZERYEcrbwA4n6q7vrBg==\"}] }}}}"
#define JOB_DOC_ONE_BLOCK                 "{\"clientToken\":\"0:testclient\",\"timestamp\":1602795143,\"execution\":{\"jobId\":\"AFR_OTA-testjob22\",\"status\":\"QUEUED\",\"queuedAt\":1602795128,\"lastUpdatedAt\":1602795128,\"versionNumber\":1,\"executionNumber\":1,\"jobDocument\":{\"afr_ota\":{\"protocols\":[\"HTTP\"],\"files\":[{\"filepath\":\"/test/demo\",\"filesize\": \"1024\" ,\"fileid\":0,\"certfile\":\"test.crt\",\"update_data_url\":\"https://dummy-url.com/ota.bin\",\"auth_scheme\":\"aws.s3.presigned\",\"sig-sha256-ecdsa\":\"MEQCIF2QDvww1G/kpRGZ8FYvQrok1bSZvXjXefRk7sqNcyPTAiB4dvGt8fozIY5NC0vUDJ2MY42ZERYEcrbwA4n6q7vrBg==\"}] }}}}"
#define JOB_DOC_INVALID                   "not a json"
#define JOB_DOC_INVALID_PROTOCOL          "{\"clientToken\":\"0:testclient\",\"timestamp\":1602795143,\"execution\":{\"jobId\":\"AFR_OTA-testjob20\",\"status\":\"QUEUED\",\"queuedAt\":1602795128,\"lastUpdatedAt\":1602795128,\"versionNumber\":1,\"executionNumber\":1,\"jobDocument\":{\"afr_ota\":{\"protocols\":[\"XYZ\"],\"streamname\":\"AFR_OTA-XYZ\",\"files\":[{\"filepath\":\"/test/demo\",\"filesize\":" OTA_TEST_FILE_SIZE_STR ",\"fileid\":0,\"certfile\":\"test.crt\",\"sig-sha256-ecdsa\":\"MEQCIF2QDvww1G/kpRGZ8FYvQrok1bSZvXjXefRk7sqNcyPTAiB4dvGt8fozIY5NC0vUDJ2MY42ZERYEcrbwA4n6q7vrBg==\"}] }}}}"
#define JOB_DOC_INVALID_BASE64_KEY        "{\"clientToken\":\"0:testclient\",\"timestamp\":1602795143,\"execution\":{\"jobId\":\"AFR_OTA-testjob20\",\"status\":\"QUEUED\",\"queuedAt\":1602795128,\"lastUpdatedAt\":1602795128,\"versionNumber\":1,\"executionNumber\":1,\"jobDocument\":{\"afr_ota\":{\"protocols\":[\"MQTT\"],\"streamname\":\"AFR_OTA-XYZ\",\"files\":[{\"filepath\":\"/test/demo\",\"filesize\":" OTA_TEST_FILE_SIZE_STR ",\"fileid\":0,\"certfile\":\"test.crt\",\"sig-sha256-ecdsa\":\"Zg===\"}] }}}}"
#define JOB_DOC_MISSING_KEY               "{\"clientToken\":\"0:testclient\",\"timestamp\":1602795143,\"execution\":{\"jobId\":\"AFR_OTA-testjob20\",\"status\":\"QUEUED\",\"queuedAt\":1602795128,\"lastUpdatedAt\":1602795128,\"versionNumber\":1,\"executionNumber\":1,\"jobDocument\":{\"afr_ota\":{\"protocols\":[\"MQTT\"],\"streamname\":\"AFR_OTA-XYZ\",\"files\":[{\"filepath\":\"/test/demo\",\"fileid\":0,\"certfile\":\"test.crt\",\"sig-sha256-ecdsa\":\"MEQCIF2QDvww1G/kpRGZ8FYvQrok1bSZvXjXefRk7sqNcyPTAiB4dvGt8fozIY5NC0vUDJ2MY42ZERYEcrbwA4n6q7vrBg==\"}] }}}}"
#define JOB_DOC_INVALID_NUMBER_NAN        "{\"clientToken\":\"0:testclient\",\"timestamp\":1602795143,\"execution\":{\"jobId\":\"AFR_OTA-testjob20\",\"status\":\"QUEUED\",\"queuedAt\":1602795128,\"lastUpdatedAt\":1602795128,\"versionNumber\":1,\"executionNumber\":1,\"jobDocument\":{\"afr_ota\":{\"protocols\":[\"MQTT\"],\"streamname\":\"AFR_OTA-XYZ\",\"files\":[{\"filepath\":\"/test/demo\",\"filesize\": \"NaN\",\"fileid\":\"NaN\",\"certfile\":\"test.crt\",\"sig-sha256-ecdsa\":\"MEQCIF2QDvww1G/kpRGZ8FYvQrok1bSZvXjXefRk7sqNcyPTAiB4dvGt8fozIY5NC0vUDJ2MY42ZERYEcrbwA4n6q7vrBg==\"}] }}}}"
#define JOB_DOC_INVALID_NUMBER_VAL        "{\"clientToken\":\"0:testclient\",\"timestamp\":1602795143,\"execution\":{\"jobId\":\"AFR_OTA-testjob20\",\"status\":\"QUEUED\",\"queuedAt\":1602795128,\"lastUpdatedAt\":1602795128,\"versionNumber\":1,\"executionNumber\":1,\"jobDocument\":{\"afr_ota\":{\"protocols\":[\"MQTT\"],\"streamname\":\"AFR_OTA-XYZ\",\"files\":[{\"filepath\":\"/test/demo\",\"filesize\": 19223372036854775808,\"fileid\":\"NaN\",\"certfile\":\"test.crt\",\"sig-sha256-ecdsa\":\"MEQCIF2QDvww1G/kpRGZ8FYvQrok1bSZvXjXefRk7sqNcyPTAiB4dvGt8fozIY5NC0vUDJ2MY42ZERYEcrbwA4n6q7vrBg==\"}] }}}}"
#define JOB_DOC_SERVERFILE_ID             "{\"clientToken\":\"0:testclient\",\"timestamp\":1602795143,\"execution\":{\"jobId\":\"AFR_OTA-testjob20\",\"status\":\"IN_PROGRESS\",\"statusDetails\":{\"self_test\":\"ready\",\"updatedBy\":\"0x1000000\"},\"queuedAt\":1602795128,\"lastUpdatedAt\":1602795128,\"versionNumber\":1,\"executionNumber\":1,\"jobDocument\":{\"afr_ota\":{\"protocols\":[\"MQTT\"],\"streamname\":\"AFR_OTA-XYZ\",\"files\":[{\"filepath\":\"/test/demo\",\"filesize\":" OTA_TEST_FILE_SIZE_STR ",\"fileid\":1,\"certfile\":\"test.crt\",\"sig-sha256-ecdsa\":\"MEQCIF2QDvww1G/kpRGZ8FYvQrok1bSZvXjXefRk7sqNcyPTAiB4dvGt8fozIY5NC0vUDJ2MY42ZERYEcrbwA4n6q7vrBg==\"}] }}}}"
#define JOB_DOC_MISSING_JOB_DOC           "{\"clientToken\":\"0:testclient\",\"timestamp\":1602795143,\"execution\":{\"jobId\":\"AFR_OTA-testjob20\",\"status\":\"QUEUED\",\"queuedAt\":1602795128,\"lastUpdatedAt\":1602795128,\"versionNumber\":1,\"executionNumber\":1}}"
#define JOB_DOC_MISSING_JOB_ID            "{\"clientToken\":\"0:testclient\",\"timestamp\":1602795143,\"execution\":{\"status\":\"QUEUED\",\"queuedAt\":1602795128,\"lastUpdatedAt\":1602795128,\"versionNumber\":1,\"executionNumber\":1,\"jobDocument\":{\"afr_ota\":{\"protocols\":[\"MQTT\"],\"streamname\":\"AFR_OTA-XYZ\",\"files\":[{\"filepath\":\"/test/demo\",\"filesize\":" OTA_TEST_FILE_SIZE_STR ",\"fileid\":0,\"certfile\":\"test.crt\",\"sig-sha256-ecdsa\":\"MEQCIF2QDvww1G/kpRGZ8FYvQrok1bSZvXjXefRk7sqNcyPTAiB4dvGt8fozIY5NC0vUDJ2MY42ZERYEcrbwA4n6q7vrBg==\"}] }}}}"
#define JOB_DOC_INVALID_JOB_ID            "{\"clientToken\":\"0:testclient\",\"timestamp\":1602795143,\"execution\":{\"jobId\":\"InvalidJobIdExceedingAllowedJobIdLengthInvalidJobIdExceedingAllowedJobIdLengthInvalidJobIdExceedingAllowedJobIdLength\",\"status\":\"QUEUED\",\"queuedAt\":1602795128,\"lastUpdatedAt\":1602795128,\"versionNumber\":1,\"executionNumber\":1,\"jobDocument\":{\"afr_ota\":{\"protocols\":[\"MQTT\"],\"streamname\":\"AFR_OTA-XYZ\",\"files\":[{\"filepath\":\"/test/demo\",\"filesize\":" OTA_TEST_FILE_SIZE_STR ",\"fileid\":0,\"certfile\":\"test.crt\",\"sig-sha256-ecdsa\":\"MEQCIF2QDvww1G/kpRGZ8FYvQrok1bSZvXjXefRk7sqNcyPTAiB4dvGt8fozIY5NC0vUDJ2MY42ZERYEcrbwA4n6q7vrBg==\"}] }}}}"
#define JOB_DOC_DIFFERENT_FILE_TYPE       "{\"clientToken\":\"0:testclient\",\"timestamp\":1602795143,\"execution\":{\"jobId\":\"AFR_OTA-testjob20\",\"status\":\"QUEUED\",\"queuedAt\":1602795128,\"lastUpdatedAt\":1602795128,\"versionNumber\":1,\"executionNumber\":1,\"jobDocument\":{\"afr_ota\":{\"protocols\":[\"MQTT\"],\"streamname\":\"AFR_OTA-XYZ\",\"files\":[{\"filepath\":\"/test/demo\",\"filesize\":" OTA_TEST_FILE_SIZE_STR ",\"fileid\":0,\"certfile\":\"test.crt\",\"fileType\":2,\"sig-sha256-ecdsa\":\"MEQCIF2QDvww1G/kpRGZ8FYvQrok1bSZvXjXefRk7sqNcyPTAiB4dvGt8fozIY5NC0vUDJ2MY42ZERYEcrbwA4n6q7vrBg==\"}] }}}}"
#define JOB_DOC_FILESIZE_OVERFLOW         "{\"clientToken\":\"0:testclient\",\"timestamp\":1602795143,\"execution\":{\"jobId\":\"AFR_OTA-testjob20\",\"status\":\"QUEUED\",\"queuedAt\":1602795128,\"lastUpdatedAt\":1602795128,\"versionNumber\":1,\"executionNumber\":1,\"jobDocument\":{\"afr_ota\":{\"protocols\":[\"MQTT\"],\"streamname\":\"AFR_OTA-XYZ\",\"files\":[{\"filepath\":\"/test/demo\",\"filesize\":" OTA_FILE_SIZE_OVERFLOW ",\"fileid\":0,\"certfile\":\"test.crt\",\"sig-sha256-ecdsa\":\"MEQCIF2QDvww1G/kpRGZ8FYvQrok1bSZvXjXefRk7sqNcyPTAiB4dvGt8fozIY5NC0vUDJ2MY42ZERYEcrbwA4n6q7vrBg==\"}] }}}}"
#define JOB_DOC_INVALID_JOB_ID_LEN_MAX    "{\"clientToken\":\"0:testclient\",\"timestamp\":1602795143,\"execution\":{\"jobId\":\"InvalidJobIdExceedingAllowedJobIdLengthInvalidJobIdExceedingAllowedJobIdL\",\"status\":\"QUEUED\",\"queuedAt\":1602795128,\"lastUpdatedAt\":1602795128,\"versionNumber\":1,\"executionNumber\":1,\"jobDocument\":{\"afr_ota\":{\"protocols\":[\"MQTT\"],\"streamname\":\"AFR_OTA-XYZ\",\"files\":[{\"filepath\":\"/test/demo\",\"filesize\":" OTA_TEST_FILE_SIZE_STR ",\"fileid\":0,\"certfile\":\"test.crt\",\"sig-sha256-ecdsa\":\"MEQCIF2QDvww1G/kpRGZ8FYvQrok1bSZvXjXefRk7sqNcyPTAiB4dvGt8fozIY5NC0vUDJ2MY42ZERYEcrbwA4n6q7vrBg==\"}] }}}}"

/* OTA application buffer size. */
#define OTA_UPDATE_FILE_PATH_SIZE         100
#define OTA_CERT_FILE_PATH_SIZE           100
#define OTA_STREAM_NAME_SIZE              50
#define OTA_INVALID_STREAM_NAME_SIZE      5 /* Size insufficient to hold stream name used in the default job document (AFR_OTA-testjob20). */
#define OTA_DECODE_MEMORY_SIZE            OTA_FILE_BLOCK_SIZE
#define OTA_FILE_BITMAP_SIZE              50
#define OTA_UPDATE_URL_SIZE               100
#define OTA_AUTH_SCHEME_SIZE              50
#define OTA_APP_BUFFER_SIZE       \
    ( OTA_UPDATE_FILE_PATH_SIZE + \
      OTA_CERT_FILE_PATH_SIZE +   \
      OTA_STREAM_NAME_SIZE +      \
      OTA_DECODE_MEMORY_SIZE +    \
      OTA_FILE_BITMAP_SIZE +      \
      OTA_UPDATE_URL_SIZE +       \
      OTA_AUTH_SCHEME_SIZE )

#define min( x, y )    ( x < y ? x : y )

#define OTA_NUM_MSG_Q_ENTRIES    20

/**
 * @brief Offset helper.
 */
#define U16_OFFSET( type, member )    ( ( uint16_t ) offsetof( type, member ) )

/* Firmware version. */
const AppVersion32_t appFirmwareVersion =
{
    .u.x.major = 1,
    .u.x.minor = 0,
    .u.x.build = 1,
};

/* OTA code signing signature algorithm. */
const char OTA_JsonFileSignatureKey[ OTA_FILE_SIG_KEY_STR_MAX_LENGTH ] = "sig-sha256-ecdsa";

/* OTA client name. */
static const char * pOtaDefaultClientId = "ota_utest";

/* OTA job doc. */
static const char * pOtaJobDoc = NULL;

/* OTA interface. */
static OtaInterfaces_t otaInterfaces;

/* OTA image state. */
static OtaPalImageState_t palImageState = OtaPalImageStateUnknown;
static bool resetCalled = false;

/* OTA application buffer. */
static OtaAppBuffer_t pOtaAppBuffer;
static uint8_t pUserBuffer[ OTA_APP_BUFFER_SIZE ];

/* OTA Event. */
static OtaEventMsg_t otaEventQueue[ OTA_NUM_MSG_Q_ENTRIES ];
static OtaEventMsg_t * otaEventQueueEnd = otaEventQueue;
static OtaEventData_t eventBuffer;
static bool eventIgnore;

/* OTA File handle and buffer. */
static FILE * pOtaFileHandle = NULL;
static uint8_t pOtaFileBuffer[ OTA_TEST_FILE_SIZE ];

/* 2 seconds default wait time for OTA state machine transition. */
static const int otaDefaultWait = 0;

/* Flag to unsubscribe to topics after ota shutdown. */
static const uint8_t unsubscribeFlag = 1;

/* Larger job name buffer to simulate if local buffer is larger than buffer in agent context. */
static uint8_t pLargerJobNameBuffer[ OTA_JOB_ID_MAX_SIZE * 2 ];

/* A counter to record how many file blocks are received. */
static int otaReceivedFileBlockNumber = 0;

/* A boolean reflecting the state of the self-test timer. */
static bool bSelfTestTimerIsActive = false;

/* A boolean reflecting the state of the data request timer. */
static bool bRequestTimerIsActive = false;

/* ========================================================================== */

/* Global static variable defined in ota.c for managing the state machine. */
extern OtaAgentContext_t otaAgent;

/* Global static variable defined in ota.c for managing the data interface
 * protocol function pointers. */
extern OtaDataInterface_t otaDataInterface;

/* Global static variable defined in ota.c for managing the control interface
 * protocol function pointers. */
extern OtaControlInterface_t otaControlInterface;

/* The OTA job document model. */
extern const JsonDocParam_t * otaJobDocModelParamStructure;

/* Static function defined in ota.c for processing events. */
extern void receiveAndProcessOtaEvent( void );

/* Static state machine function handlers under test defined in ota.c. */
extern OtaErr_t initFileHandler( const OtaEventData_t * pEventData );
extern OtaErr_t requestDataHandler( const OtaEventData_t * pEventData );
extern OtaErr_t requestJobHandler( const OtaEventData_t * pEventData );
extern OtaErr_t processDataHandler( const OtaEventData_t * pEventData );
extern OtaErr_t resumeHandler( const OtaEventData_t * pEventData );
extern OtaErr_t jobNotificationHandler( const OtaEventData_t * pEventData );
extern OtaErr_t shutdownHandler( const OtaEventData_t * pEventData );

/* Static helper functions under test defined in ota.c. */
extern OtaErr_t setImageStateWithReason( OtaImageState_t stateToSet,
                                         uint32_t reasonToSet );
extern bool otaClose( OtaFileContext_t * const pFileContext );
extern bool validateDataBlock( const OtaFileContext_t * pFileContext,
                               uint32_t blockIndex,
                               uint32_t blockSize );

extern DocParseErr_t initDocModel( JsonDocModel_t * pDocModel,
                                   const JsonDocParam_t * pBodyDef,
                                   void * contextBaseAddr,
                                   uint32_t contextSize,
                                   uint16_t numJobParams );

extern OtaFileContext_t * parseJobDoc( const JsonDocParam_t * pJsonDoc,
                                       uint16_t numJobParams,
                                       const char * pJson,
                                       uint32_t messageLength,
                                       bool * pUpdateJob );

extern DocParseErr_t validateJSON( const char * pJson,
                                   uint32_t messageLength );

extern IngestResult_t ingestDataBlockCleanup( OtaFileContext_t * pFileContext,
                                              OtaPalStatus_t * pCloseResult );

extern OtaJobParseErr_t verifyActiveJobStatus( OtaFileContext_t * pFileContext,
                                               OtaFileContext_t ** pFinalFile,
                                               bool * pUpdateJob );

/* ========================================================================== */
/* ====================== Unit test helper functions ======================== */
/* ========================================================================== */

static void * mockMallocAlwaysFail( size_t size )
{
    ( void ) size;
    return NULL;
}

static OtaOsStatus_t mockOSEventReset( OtaEventContext_t * unused )
{
    otaEventQueueEnd = otaEventQueue;
    eventIgnore = false;

    ( void ) unused;

    return OtaOsSuccess;
}

/* Allow an event to be sent only once, after that ignore all incoming event. Useful to make sure
 * internal OTA handler are not able to send any event. */
static OtaOsStatus_t mockOSEventSendThenStop( OtaEventContext_t * unused_1,
                                              const void * pEventMsg,
                                              uint32_t unused_2 )
{
    ( void ) unused_1;
    ( void ) unused_2;

    if( otaEventQueueEnd >= otaEventQueue + OTA_NUM_MSG_Q_ENTRIES )
    {
        return OtaOsEventQueueSendFailed;
    }

    if( !eventIgnore )
    {
        const OtaEventMsg_t * pOtaEvent = pEventMsg;

        otaEventQueueEnd->eventId = pOtaEvent->eventId;
        otaEventQueueEnd->pEventData = pOtaEvent->pEventData;
        otaEventQueueEnd++;

        eventIgnore = true;
    }

    return OtaOsSuccess;
}

/* A variant of mockOSEventSendThenStop, but return failure after first event sent. */
static OtaOsStatus_t mockOSEventSendThenFail( OtaEventContext_t * unused_1,
                                              const void * pEventMsg,
                                              uint32_t unused_2 )
{
    OtaOsStatus_t err = OtaOsSuccess;

    ( void ) unused_1;
    ( void ) unused_2;

    if( eventIgnore )
    {
        err = OtaOsEventQueueSendFailed;
    }
    else
    {
        err = mockOSEventSendThenStop( unused_1, pEventMsg, unused_2 );
    }

    return err;
}

/* Allow events to be sent any number of times. */
static OtaOsStatus_t mockOSEventSend( OtaEventContext_t * unused_1,
                                      const void * pEventMsg,
                                      uint32_t unused_2 )
{
    ( void ) unused_1;
    ( void ) unused_2;

    if( otaEventQueueEnd >= otaEventQueue + OTA_NUM_MSG_Q_ENTRIES )
    {
        return OtaOsEventQueueSendFailed;
    }

    const OtaEventMsg_t * pOtaEvent = pEventMsg;

    otaEventQueueEnd->eventId = pOtaEvent->eventId;
    otaEventQueueEnd->pEventData = pOtaEvent->pEventData;
    otaEventQueueEnd++;

    return OtaOsSuccess;
}

/* Ignore all incoming events and return fail. */
static OtaOsStatus_t mockOSEventSendAlwaysFail( OtaEventContext_t * unused_1,
                                                const void * pEventMsg,
                                                uint32_t unused_2 )
{
    ( void ) unused_1;
    ( void ) pEventMsg;
    ( void ) unused_2;

    return OtaOsEventQueueSendFailed;
}

static OtaOsStatus_t mockOSEventReceive( OtaEventContext_t * unused_1,
                                         void * pEventMsg,
                                         uint32_t unused_2 )
{
    OtaOsStatus_t err = OtaOsSuccess;
    OtaEventMsg_t * pOtaEvent = pEventMsg;
    size_t currQueueSize = otaEventQueueEnd - otaEventQueue;

    ( void ) unused_1;
    ( void ) unused_2;

    if( otaEventQueueEnd != otaEventQueue )
    {
        pOtaEvent->eventId = otaEventQueue[ 0 ].eventId;
        pOtaEvent->pEventData = otaEventQueue[ 0 ].pEventData;
        memmove( otaEventQueue, otaEventQueue + 1, sizeof( OtaEventMsg_t ) * ( currQueueSize - 1 ) );
        otaEventQueueEnd--;
    }
    else
    {
        err = OtaOsEventQueueReceiveFailed;
    }

    return err;
}

static OtaOsStatus_t stubOSTimerStart( OtaTimerId_t timerId,
                                       const char * const pTimerName,
                                       const uint32_t timeout,
                                       OtaTimerCallback_t callback )
{
    ( void ) timerId;
    ( void ) pTimerName;
    ( void ) timeout;
    ( void ) callback;
    return OtaOsSuccess;
}

static OtaOsStatus_t mockOSTimerStart( OtaTimerId_t timerId,
                                       const char * const pTimerName,
                                       const uint32_t timeout,
                                       OtaTimerCallback_t callback )
{
    if( timerId == OtaRequestTimer )
    {
        bRequestTimerIsActive = true;
    }
    else if( timerId == OtaSelfTestTimer )
    {
        bSelfTestTimerIsActive = true;
    }

    ( void ) pTimerName;
    ( void ) timeout;
    ( void ) callback;
    return OtaOsSuccess;
}

static OtaOsStatus_t mockOSTimerInvokeCallback( OtaTimerId_t timerId,
                                                const char * const pTimerName,
                                                const uint32_t timeout,
                                                OtaTimerCallback_t callback )
{
    callback( timerId );
    ( void ) timeout;
    ( void ) pTimerName;
    return OtaOsSuccess;
}

static OtaOsStatus_t mockOSTimerStartAlwaysFail( OtaTimerId_t unused_1,
                                                 const char * const unused_2,
                                                 const uint32_t unused_3,
                                                 OtaTimerCallback_t unused_4 )
{
    ( void ) unused_1;
    ( void ) unused_2;
    ( void ) unused_3;
    ( void ) unused_4;
    return OtaOsTimerStartFailed;
}

static OtaOsStatus_t stubOSTimerStop( OtaTimerId_t timerId )
{
    ( void ) timerId;
    return OtaOsSuccess;
}

static OtaOsStatus_t mockOSTimerStop( OtaTimerId_t timerId )
{
    if( timerId == OtaRequestTimer )
    {
        bRequestTimerIsActive = false;
    }
    else if( timerId == OtaSelfTestTimer )
    {
        bSelfTestTimerIsActive = false;
    }

    return OtaOsSuccess;
}

static OtaOsStatus_t stubOSTimerDelete( OtaTimerId_t timerId )
{
    ( void ) timerId;
    return OtaOsSuccess;
}

static OtaMqttStatus_t stubMqttSubscribe( const char * unused_1,
                                          uint16_t unused_2,
                                          uint8_t unused_3 )
{
    ( void ) unused_1;
    ( void ) unused_2;
    ( void ) unused_3;

    return OtaMqttSuccess;
}

static OtaMqttStatus_t stubMqttSubscribeAlwaysFail( const char * unused_1,
                                                    uint16_t unused_2,
                                                    uint8_t unused_3 )
{
    ( void ) unused_1;
    ( void ) unused_2;
    ( void ) unused_3;

    return OtaMqttSubscribeFailed;
}

static OtaMqttStatus_t stubMqttPublish( const char * const unused_1,
                                        uint16_t unused_2,
                                        const char * unused_3,
                                        uint32_t unused_4,
                                        uint8_t unused_5 )
{
    ( void ) unused_1;
    ( void ) unused_2;
    ( void ) unused_3;
    ( void ) unused_4;
    ( void ) unused_5;

    return OtaMqttSuccess;
}

OtaErr_t mockControlInterfaceRequestJobAlwaysFail( const OtaAgentContext_t * unused )
{
    ( void ) unused;

    return OtaErrRequestJobFailed;
}

OtaErr_t mockControlInterfaceUpdateJobAlwaysFail( const OtaAgentContext_t * unused1,
                                                  OtaJobStatus_t unused2,
                                                  int32_t unused3,
                                                  int32_t unused4 )
{
    ( void ) unused1;
    ( void ) unused2;
    ( void ) unused3;
    ( void ) unused4;

    return OtaErrUpdateJobStatusFailed;
}

OtaErr_t mockControlInterfaceUpdateJobCount( const OtaAgentContext_t * unused1,
                                             OtaJobStatus_t status,
                                             int32_t unused3,
                                             int32_t unused4 )
{
    ( void ) unused1;
    ( void ) unused3;
    ( void ) unused4;

    if( ( status == JobStatusInProgress ) || ( status == JobStatusSucceeded ) )
    {
        otaReceivedFileBlockNumber++;
    }

    return OtaErrNone;
}

OtaErr_t mockDataInterfaceInitFileTransferAlwaysFail( const OtaAgentContext_t * unused )
{
    ( void ) unused;

    return OtaErrInitFileTransferFailed;
}


OtaErr_t mockDataInitFileTransferAlwaysSucceed( const OtaAgentContext_t * unused )
{
    ( void ) unused;

    return OtaErrNone;
}

static OtaMqttStatus_t stubMqttPublishAlwaysFail( const char * const unused_1,
                                                  uint16_t unused_2,
                                                  const char * unused_3,
                                                  uint32_t unused_4,
                                                  uint8_t unused_5 )
{
    ( void ) unused_1;
    ( void ) unused_2;
    ( void ) unused_3;
    ( void ) unused_4;
    ( void ) unused_5;

    return OtaMqttPublishFailed;
}

static OtaMqttStatus_t stubMqttUnsubscribe( const char * unused_1,
                                            uint16_t unused_2,
                                            uint8_t unused_3 )
{
    ( void ) unused_1;
    ( void ) unused_2;
    ( void ) unused_3;

    return OtaMqttSuccess;
}

static OtaMqttStatus_t stubMqttUnsubscribeAlwaysFail( const char * unused_1,
                                                      uint16_t unused_2,
                                                      uint8_t unused_3 )
{
    ( void ) unused_1;
    ( void ) unused_2;
    ( void ) unused_3;

    return OtaMqttUnsubscribeFailed;
}

static OtaHttpStatus_t stubHttpInit( char * url )
{
    ( void ) url;

    return OtaHttpSuccess;
}

static OtaHttpStatus_t mockHttpInitAlwaysFail( char * url )
{
    ( void ) url;
    return OtaHttpInitFailed;
}

static OtaHttpStatus_t stubHttpRequest( uint32_t rangeStart,
                                        uint32_t rangeEnd )
{
    ( void ) rangeEnd;
    ( void ) rangeStart;
    return OtaHttpSuccess;
}

static OtaHttpStatus_t mockHttpRequestAlwaysFail( uint32_t rangeStart,
                                                  uint32_t rangeEnd )
{
    ( void ) rangeEnd;
    ( void ) rangeStart;

    return OtaHttpRequestFailed;
}

static OtaHttpStatus_t stubHttpDeinit()
{
    return OtaHttpSuccess;
}

static OtaHttpStatus_t stubHttpDeinitAlwaysFail()
{
    return OtaHttpDeinitFailed;
}

OtaPalStatus_t mockPalAbort( OtaFileContext_t * const pFileContext )
{
    ( void ) pFileContext;

    return OTA_PAL_COMBINE_ERR( OtaPalSuccess, 0 );
}

OtaPalStatus_t mockPalCreateFileForRx( OtaFileContext_t * const pFileContext )
{
    pOtaFileHandle = ( FILE * ) pOtaFileBuffer;
    pFileContext->pFile = pOtaFileHandle;
    return OTA_PAL_COMBINE_ERR( OtaPalSuccess, 0 );
}

OtaPalStatus_t mockPalCreateNullFileForRx( OtaFileContext_t * const pFileContext )
{
    pFileContext->pFile = NULL;
    return OTA_PAL_COMBINE_ERR( OtaPalSuccess, 0 );
}

OtaPalStatus_t mockPalCreateFileForRxAlwaysFail( OtaFileContext_t * const pFileContext )
{
    ( void ) pFileContext;
    return OTA_PAL_COMBINE_ERR( OtaPalRxFileCreateFailed, 0 );
}


OtaPalStatus_t mockPalCloseFile( OtaFileContext_t * const pFileContext )
{
    ( void ) pFileContext;
    return OTA_PAL_COMBINE_ERR( OtaPalSuccess, 0 );
}

OtaPalStatus_t mockPalCloseFileAlwaysFail( OtaFileContext_t * const pFileContext )
{
    ( void ) pFileContext;
    return OTA_PAL_COMBINE_ERR( OtaPalFileClose, 0 );
}

OtaPalStatus_t mockPalCloseFileSigCheckFail( OtaFileContext_t * const pFileContext )
{
    ( void ) pFileContext;
    return OTA_PAL_COMBINE_ERR( OtaPalSignatureCheckFailed, 0 );
}

int16_t mockPalWriteBlock( OtaFileContext_t * const pFileContext,
                           uint32_t offset,
                           uint8_t * const pData,
                           uint32_t blockSize )
{
    ( void ) pFileContext;

    if( offset >= OTA_TEST_FILE_SIZE )
    {
        TEST_ASSERT_TRUE_MESSAGE( false, "Offset is bigger than test file buffer." );
    }

    memcpy( pOtaFileBuffer + offset, pData, blockSize );
    return blockSize;
}

int16_t mockPalWriteBlockAlwaysFail( OtaFileContext_t * const unused1,
                                     uint32_t unused2,
                                     uint8_t * const unused3,
                                     uint32_t unused4 )
{
    ( void ) unused1;
    ( void ) unused2;
    ( void ) unused3;
    ( void ) unused4;

    return -1;
}

int16_t mockPalWriteBlockPartialWrite( OtaFileContext_t * const unused1,
                                       uint32_t unused2,
                                       uint8_t * const unused3,
                                       uint32_t unused4 )
{
    ( void ) unused1;
    ( void ) unused2;
    ( void ) unused3;
    ( void ) unused4;

    return 1;
}

OtaPalStatus_t mockPalActivate( OtaFileContext_t * const pFileContext )
{
    ( void ) pFileContext;
    return OTA_PAL_COMBINE_ERR( OtaPalSuccess, 0 );
}

OtaPalStatus_t mockPalActivateReturnFail( OtaFileContext_t * const pFileContext )
{
    ( void ) pFileContext;
    return OTA_PAL_COMBINE_ERR( OtaPalActivateFailed, 0 );
}

OtaPalStatus_t mockPalResetDevice( OtaFileContext_t * const pFileContext )
{
    ( void ) pFileContext;
    resetCalled = true;
    return OTA_PAL_COMBINE_ERR( OtaPalSuccess, 0 );
}

OtaPalStatus_t mockPalSetPlatformImageState( OtaFileContext_t * const pFileContext,
                                             OtaImageState_t eState )
{
    ( void ) pFileContext;

    switch( eState )
    {
        case OtaImageStateTesting:
            palImageState = OtaPalImageStatePendingCommit;
            break;

        case OtaImageStateAccepted:
            palImageState = OtaPalImageStateValid;
            break;

        default:
            palImageState = OtaPalImageStateInvalid;
            break;
    }

    return OTA_PAL_COMBINE_ERR( OtaPalSuccess, 0 );
}

OtaPalStatus_t mockPalSetPlatformImageStateAlwaysFail( OtaFileContext_t * const pFileContext,
                                                       OtaImageState_t eState )
{
    ( void ) pFileContext;
    ( void ) eState;
    return OTA_PAL_COMBINE_ERR( OtaPalBadImageState, 0 );
}

OtaPalImageState_t mockPalGetPlatformImageState( OtaFileContext_t * const pFileContext )
{
    ( void ) pFileContext;
    return palImageState;
}

OtaPalImageState_t mockPalGetPlatformImageStateAlwaysInvalid( OtaFileContext_t * const pFileContext )
{
    ( void ) pFileContext;
    return OtaPalImageStateInvalid;
}

OtaPalImageState_t mockPalGetPlatformImageStateAlwaysPendingCommit( OtaFileContext_t * const pFileContext )
{
    ( void ) pFileContext;
    return OtaPalImageStatePendingCommit;
}

static void mockAppCallback( OtaJobEvent_t event,
                             void * pData )
{
    OtaJobDocument_t * jobDoc = NULL;

    ( void ) pData;

    if( event == OtaJobEventStartTest )
    {
        OTA_SetImageState( OtaImageStateAccepted );
    }

    if( event == OtaJobEventParseCustomJob )
    {
        jobDoc = ( OtaJobDocument_t * ) pData;
        jobDoc->parseErr = OtaJobParseErrNone;
    }
}

static void mockAppCallbackCustomParsingFails( OtaJobEvent_t event,
                                               void * pData )
{
    OtaJobDocument_t * jobDoc = NULL;

    ( void ) pData;

    if( event == OtaJobEventStartTest )
    {
        OTA_SetImageState( OtaImageStateAccepted );
    }

    if( event == OtaJobEventParseCustomJob )
    {
        jobDoc = ( OtaJobDocument_t * ) pData;
        jobDoc->parseErr = OtaJobParseErrUnknown;
    }
}

/* Set default OTA OS interface to mockOSEventSendThenStop. This allows us to easily control the
 * state machine transition by blocking any event in OTA internal handlers. */
static void otaInterfaceDefault()
{
    otaInterfaces.os.event.init = mockOSEventReset;
    otaInterfaces.os.event.send = mockOSEventSendThenStop;
    otaInterfaces.os.event.recv = mockOSEventReceive;
    otaInterfaces.os.event.deinit = mockOSEventReset;

    otaInterfaces.os.timer.start = stubOSTimerStart;
    otaInterfaces.os.timer.stop = stubOSTimerStop;
    otaInterfaces.os.timer.delete = stubOSTimerDelete;

    otaInterfaces.os.mem.malloc = malloc;
    otaInterfaces.os.mem.free = free;

    otaInterfaces.mqtt.subscribe = stubMqttSubscribe;
    otaInterfaces.mqtt.publish = stubMqttPublish;
    otaInterfaces.mqtt.unsubscribe = stubMqttUnsubscribe;

    otaInterfaces.http.init = stubHttpInit;
    otaInterfaces.http.deinit = stubHttpDeinit;
    otaInterfaces.http.request = stubHttpRequest;

    otaInterfaces.pal.abort = mockPalAbort;
    otaInterfaces.pal.createFile = mockPalCreateFileForRx;
    otaInterfaces.pal.closeFile = mockPalCloseFile;
    otaInterfaces.pal.writeBlock = mockPalWriteBlock;
    otaInterfaces.pal.activate = mockPalActivate;
    otaInterfaces.pal.reset = mockPalResetDevice;
    otaInterfaces.pal.setPlatformImageState = mockPalSetPlatformImageState;
    otaInterfaces.pal.getPlatformImageState = mockPalGetPlatformImageState;
}

static void otaAppBufferDefault()
{
    pOtaAppBuffer.pUpdateFilePath = pUserBuffer;
    pOtaAppBuffer.updateFilePathsize = OTA_UPDATE_FILE_PATH_SIZE;
    pOtaAppBuffer.pCertFilePath = pOtaAppBuffer.pUpdateFilePath + pOtaAppBuffer.updateFilePathsize;
    pOtaAppBuffer.certFilePathSize = OTA_CERT_FILE_PATH_SIZE;
    pOtaAppBuffer.pStreamName = pOtaAppBuffer.pCertFilePath + pOtaAppBuffer.certFilePathSize;
    pOtaAppBuffer.streamNameSize = OTA_STREAM_NAME_SIZE;
    pOtaAppBuffer.pDecodeMemory = pOtaAppBuffer.pStreamName + pOtaAppBuffer.streamNameSize;
    pOtaAppBuffer.decodeMemorySize = OTA_DECODE_MEMORY_SIZE;
    pOtaAppBuffer.pFileBitmap = pOtaAppBuffer.pDecodeMemory + pOtaAppBuffer.decodeMemorySize;
    pOtaAppBuffer.fileBitmapSize = OTA_FILE_BITMAP_SIZE;
    pOtaAppBuffer.pUrl = pOtaAppBuffer.pStreamName + pOtaAppBuffer.streamNameSize;
    pOtaAppBuffer.urlSize = OTA_UPDATE_URL_SIZE;
    pOtaAppBuffer.pAuthScheme = pOtaAppBuffer.pUrl + pOtaAppBuffer.urlSize;
    pOtaAppBuffer.authSchemeSize = OTA_AUTH_SCHEME_SIZE;
}

/* Helper function for processing all elements in the queue if there are any. */
static void processEntireQueue()
{
    if( otaEventQueueEnd >= otaEventQueue + OTA_NUM_MSG_Q_ENTRIES )
    {
        return;
    }

    while( otaEventQueueEnd != otaEventQueue )
    {
        receiveAndProcessOtaEvent();
    }
}

static void otaInit( const char * pClientID,
                     OtaAppCallback_t appCallback )
{
    OTA_Init( &pOtaAppBuffer,
              &otaInterfaces,
              ( const uint8_t * ) pClientID,
              appCallback );
}

static void otaInitDefault()
{
    otaInit( pOtaDefaultClientId, mockAppCallback );
}

static void otaDeinit()
{
    mockOSEventReset( NULL );
    OTA_Shutdown( otaDefaultWait, unsubscribeFlag );
    processEntireQueue();
}

static void otaReceiveJobDocument()
{
    TEST_ASSERT_NOT_EQUAL( NULL, pOtaJobDoc );
    size_t job_doc_len = strlen( pOtaJobDoc );
    OtaEventMsg_t otaEvent = { 0 };

    /* Parse success would create the file, let it invoke our mock when creating file. */
    otaEvent.eventId = OtaAgentEventReceivedJobDocument;
    otaEvent.pEventData = &eventBuffer;
    memcpy( otaEvent.pEventData->data, pOtaJobDoc, job_doc_len );
    otaEvent.pEventData->dataLength = job_doc_len;
    OTA_SignalEvent( &otaEvent );
}

/* Jump to any state in OTA agent. The event send interface must be set to
 * mockOSEventSendThenStop to prevent any OTA internal state transitions. */
static void otaGoToState( OtaState_t state )
{
    OtaEventMsg_t otaEvent = { 0 };

    if( state == OTA_GetState() )
    {
        return;
    }

    if( OtaAgentStateStopped == OTA_GetState() )
    {
        otaInitDefault();
    }

    /* Default to the MQTT job doc. */
    if( pOtaJobDoc == NULL )
    {
        pOtaJobDoc = JOB_DOC_A;
    }

    switch( state )
    {
        case OtaAgentStateInit:

            /* Nothing needs to be done here since we should either be in init state already or
             * we are in other running states. */
            break;

        case OtaAgentStateReady:
            otaAgent.state = OtaAgentStateReady;
            break;

        case OtaAgentStateRequestingJob:
            otaGoToState( OtaAgentStateReady );
            otaEvent.eventId = OtaAgentEventStart;
            OTA_SignalEvent( &otaEvent );
            receiveAndProcessOtaEvent();
            break;

        case OtaAgentStateWaitingForJob:
            otaGoToState( OtaAgentStateRequestingJob );
            otaEvent.eventId = OtaAgentEventRequestJobDocument;
            OTA_SignalEvent( &otaEvent );
            receiveAndProcessOtaEvent();
            break;

        case OtaAgentStateCreatingFile:
            otaGoToState( OtaAgentStateWaitingForJob );
            otaReceiveJobDocument();
            receiveAndProcessOtaEvent();
            break;

        case OtaAgentStateRequestingFileBlock:
            otaGoToState( OtaAgentStateCreatingFile );
            otaEvent.eventId = OtaAgentEventCreateFile;
            OTA_SignalEvent( &otaEvent );
            receiveAndProcessOtaEvent();
            break;

        case OtaAgentStateWaitingForFileBlock:
            otaGoToState( OtaAgentStateRequestingFileBlock );
            otaEvent.eventId = OtaAgentEventRequestFileBlock;
            OTA_SignalEvent( &otaEvent );
            receiveAndProcessOtaEvent();
            break;

        case OtaAgentStateSuspended:
            otaGoToState( OtaAgentStateReady );
            OTA_Suspend();
            receiveAndProcessOtaEvent();
            break;

        default:
            break;
    }

    mockOSEventReset( NULL );
}

/* ========================================================================== */
/* ================ Unit test setup and tear down functions ================= */
/* ========================================================================== */

void setUp()
{
    TEST_ASSERT_EQUAL( OtaAgentStateStopped, OTA_GetState() );
    otaInterfaceDefault();
    otaAppBufferDefault();

    otaReceivedFileBlockNumber = 0;
}

void tearDown()
{
    palImageState = OtaPalImageStateUnknown;
    resetCalled = false;
    pOtaJobDoc = NULL;
    pOtaFileHandle = NULL;
    memset( pOtaFileBuffer, 0, OTA_TEST_FILE_SIZE );
    otaInterfaceDefault();
    otaDeinit();
    TEST_ASSERT_EQUAL( OtaAgentStateStopped, OTA_GetState() );
}

/* ========================================================================== */
/* =============================== Unit tests =============================== */
/* ========================================================================== */

void test_OTA_InitWhenStopped()
{
    otaGoToState( OtaAgentStateInit );
    TEST_ASSERT_EQUAL( OtaAgentStateInit, OTA_GetState() );
}

void test_OTA_InitWhenReady()
{
    otaGoToState( OtaAgentStateReady );
    TEST_ASSERT_EQUAL( OtaAgentStateReady, OTA_GetState() );

    /* Calling init again should remain in ready state. */
    otaInitDefault();
    TEST_ASSERT_EQUAL( OtaAgentStateReady, OTA_GetState() );

    /* Explicitly test NULL client name and NULL complete callback. */
    otaInit( NULL, NULL );
    TEST_ASSERT_EQUAL( OtaAgentStateReady, OTA_GetState() );
}

void test_OTA_InitWithNullName()
{
    /* Explicitly test NULL client name. OTA agent should remain in stopped state. */
    otaInit( NULL, mockAppCallback );
    TEST_ASSERT_EQUAL( OtaAgentStateStopped, OTA_GetState() );
}

void test_OTA_InitWithNameTooLong()
{
    /* OTA does not accept name longer than 64. Explicitly test long client name. */
    char long_name[ 100 ] = { 0 };

    memset( long_name, 1, sizeof( long_name ) - 1 );
    otaInit( long_name, mockAppCallback );
    TEST_ASSERT_EQUAL( OtaAgentStateStopped, OTA_GetState() );
}

void test_OTA_InitNullAppBuffers()
{
    /* Test for having NULL pointers but valid sizes. */
    pOtaAppBuffer.pUpdateFilePath = NULL;
    pOtaAppBuffer.updateFilePathsize = OTA_UPDATE_FILE_PATH_SIZE;
    pOtaAppBuffer.pCertFilePath = NULL;
    pOtaAppBuffer.certFilePathSize = OTA_CERT_FILE_PATH_SIZE;
    pOtaAppBuffer.pStreamName = NULL;
    pOtaAppBuffer.streamNameSize = OTA_STREAM_NAME_SIZE;
    pOtaAppBuffer.pDecodeMemory = NULL;
    pOtaAppBuffer.decodeMemorySize = OTA_DECODE_MEMORY_SIZE;
    pOtaAppBuffer.pFileBitmap = NULL;
    pOtaAppBuffer.fileBitmapSize = OTA_FILE_BITMAP_SIZE;
    pOtaAppBuffer.pUrl = NULL;
    pOtaAppBuffer.urlSize = OTA_UPDATE_URL_SIZE;
    pOtaAppBuffer.pAuthScheme = NULL;
    pOtaAppBuffer.authSchemeSize = OTA_AUTH_SCHEME_SIZE;

    OTA_Init( &pOtaAppBuffer,
              &otaInterfaces,
              ( const uint8_t * ) pOtaDefaultClientId,
              mockAppCallback );
    TEST_ASSERT_EQUAL( OtaAgentStateInit, OTA_GetState() );
}

void test_OTA_InitZeroAppBufferSizes()
{
    /* Test for having valid pointers with zero sizes. */
    pOtaAppBuffer.pUpdateFilePath = pUserBuffer;
    pOtaAppBuffer.updateFilePathsize = 0;
    pOtaAppBuffer.pCertFilePath = pUserBuffer;
    pOtaAppBuffer.certFilePathSize = 0;
    pOtaAppBuffer.pStreamName = pUserBuffer;
    pOtaAppBuffer.streamNameSize = 0;
    pOtaAppBuffer.pDecodeMemory = pUserBuffer;
    pOtaAppBuffer.decodeMemorySize = 0;
    pOtaAppBuffer.pFileBitmap = pUserBuffer;
    pOtaAppBuffer.fileBitmapSize = 0;
    pOtaAppBuffer.pUrl = pUserBuffer;
    pOtaAppBuffer.urlSize = 0;
    pOtaAppBuffer.pAuthScheme = pUserBuffer;
    pOtaAppBuffer.authSchemeSize = 0;

    OTA_Init( &pOtaAppBuffer,
              &otaInterfaces,
              ( const uint8_t * ) pOtaDefaultClientId,
              mockAppCallback );
    TEST_ASSERT_EQUAL( OtaAgentStateInit, OTA_GetState() );
}

void test_OTA_ShutdownWithDelay()
{
    otaGoToState( OtaAgentStateReady );
    OTA_Shutdown( 2000, 0 );
    receiveAndProcessOtaEvent();
    TEST_ASSERT_EQUAL( OtaAgentStateStopped, OTA_GetState() );
}

void test_OTA_ShutdownWhenStopped()
{
    /* Calling shutdown when already stopped should have no effect. */
    OTA_Shutdown( otaDefaultWait, unsubscribeFlag );
    receiveAndProcessOtaEvent();
    TEST_ASSERT_EQUAL( OtaAgentStateStopped, OTA_GetState() );
}

void test_OTA_ShutdownFailToSendEvent()
{
    otaGoToState( OtaAgentStateReady );
    TEST_ASSERT_EQUAL( OtaAgentStateReady, OTA_GetState() );

    /* Set the event send interface to a mock function that always fail. */
    otaInterfaces.os.event.send = mockOSEventSendAlwaysFail;

    /* Shutdown should now fail and OTA agent should remain in ready state. */
    OTA_Shutdown( otaDefaultWait, unsubscribeFlag );
    receiveAndProcessOtaEvent();
    TEST_ASSERT_EQUAL( OtaAgentStateReady, OTA_GetState() );
}

void test_OTA_ShutdownTwiceBeforeProcessing()
{
    otaInterfaces.os.event.send = mockOSEventSend;

    otaGoToState( OtaAgentStateReady );
    OTA_Shutdown( 0, 0 );
    OTA_Shutdown( 0, 0 );
    receiveAndProcessOtaEvent();
    receiveAndProcessOtaEvent();
    TEST_ASSERT_EQUAL( OtaAgentStateStopped, OTA_GetState() );
}

void test_OTA_CloseNullInput()
{
    TEST_ASSERT_EQUAL( false, otaClose( NULL ) );
}

void test_OTA_StartWhenReady()
{
    OtaEventMsg_t otaEvent = { 0 };

    /* Let the PAL says it's not in self test.*/
    palImageState = OtaPalImageStateValid;

    otaGoToState( OtaAgentStateReady );
    TEST_ASSERT_EQUAL( OtaAgentStateReady, OTA_GetState() );

    otaEvent.eventId = OtaAgentEventStart;
    OTA_SignalEvent( &otaEvent );
    receiveAndProcessOtaEvent();
    TEST_ASSERT_EQUAL( OtaAgentStateRequestingJob, OTA_GetState() );
}

void test_OTA_StartFailedWhenReady()
{
    OtaEventMsg_t otaEvent = { 0 };

    /* Let the PAL says it's not in self test.*/
    palImageState = OtaPalImageStateValid;

    otaGoToState( OtaAgentStateReady );
    TEST_ASSERT_EQUAL( OtaAgentStateReady, OTA_GetState() );

    /* Set the event send interface to a mock function that fails after first event sent. */
    otaInterfaces.os.event.send = mockOSEventSendThenFail;

    /* The event handler should fail, so OTA agent should remain in OtaAgentStateReady state. */
    otaEvent.eventId = OtaAgentEventStart;
    OTA_SignalEvent( &otaEvent );
    receiveAndProcessOtaEvent();
    TEST_ASSERT_EQUAL( OtaAgentStateReady, OTA_GetState() );
}

void test_OTA_SuspendWhenStopped()
{
    /* Calling suspend when stopped should return an error. */
    TEST_ASSERT_NOT_EQUAL( OtaErrNone, OTA_Suspend() );

    /* OTA agent should remain in stopped state. */
    TEST_ASSERT_EQUAL( OtaAgentStateStopped, OTA_GetState() );
}

void test_OTA_SuspendWhenReady()
{
    otaGoToState( OtaAgentStateReady );
    TEST_ASSERT_EQUAL( OtaAgentStateReady, OTA_GetState() );

    TEST_ASSERT_EQUAL( OtaErrNone, OTA_Suspend() );
    receiveAndProcessOtaEvent();
    TEST_ASSERT_EQUAL( OtaAgentStateSuspended, OTA_GetState() );
}

void test_OTA_SuspendFailedWhenReady()
{
    otaGoToState( OtaAgentStateReady );
    TEST_ASSERT_EQUAL( OtaAgentStateReady, OTA_GetState() );

    /* Set the event send interface to a mock function that always fail. */
    otaInterfaces.os.event.send = mockOSEventSendAlwaysFail;

    /* Suspend should fail and OTA agent should remain in ready state. */
    TEST_ASSERT_EQUAL( OtaErrSignalEventFailed, OTA_Suspend() );
    TEST_ASSERT_EQUAL( OtaAgentStateReady, OTA_GetState() );
}

void test_OTA_ResumeWhenStopped()
{
    /* Calling resume when stopped should return an error. */
    TEST_ASSERT_NOT_EQUAL( OtaErrNone, OTA_Resume() );

    /* OTA agent should remain in stopped state. */
    TEST_ASSERT_EQUAL( OtaAgentStateStopped, OTA_GetState() );
}

void test_OTA_ResumeWhenSuspended()
{
    otaGoToState( OtaAgentStateSuspended );
    TEST_ASSERT_EQUAL( OtaAgentStateSuspended, OTA_GetState() );

    TEST_ASSERT_EQUAL( OtaErrNone, OTA_Resume() );
    receiveAndProcessOtaEvent();
    TEST_ASSERT_EQUAL( OtaAgentStateRequestingJob, OTA_GetState() );
}

void test_OTA_ResumeWhenReady()
{
    otaGoToState( OtaAgentStateReady );
    TEST_ASSERT_EQUAL( OtaAgentStateReady, OTA_GetState() );

    /* Calling resume when OTA agent is not suspend state. This should be an unexpected event and
     * the agent should remain in ready state. */
    TEST_ASSERT_EQUAL( OtaErrNone, OTA_Resume() );
    receiveAndProcessOtaEvent();
    TEST_ASSERT_EQUAL( OtaAgentStateReady, OTA_GetState() );
}

void test_OTA_ResumeFailedWhenSuspended()
{
    otaGoToState( OtaAgentStateSuspended );
    TEST_ASSERT_EQUAL( OtaAgentStateSuspended, OTA_GetState() );

    /* Set the event send interface to a mock function that always fail. */
    otaInterfaces.os.event.send = mockOSEventSendAlwaysFail;

    /* Resume should fail and OTA agent should remain in suspend state. */
    TEST_ASSERT_EQUAL( OtaErrSignalEventFailed, OTA_Resume() );
    TEST_ASSERT_EQUAL( OtaAgentStateSuspended, OTA_GetState() );
}

void test_OTA_ResumeSelfTestTimerRestart()
{
    otaGoToState( OtaAgentStateSuspended );
    TEST_ASSERT_EQUAL( OtaAgentStateSuspended, OTA_GetState() );

    /* Reset timer state and configure mocked timer function for tracking timer state */
    bSelfTestTimerIsActive = false;
    bRequestTimerIsActive = false;
    otaInterfaces.os.timer.start = mockOSTimerStart;
    otaInterfaces.os.timer.stop = mockOSTimerStop;
    otaInterfaces.os.event.send = mockOSEventSend;

    /* Let the PAL always says it's in self test. */
    otaInterfaces.pal.getPlatformImageState = mockPalGetPlatformImageStateAlwaysPendingCommit;
    TEST_ASSERT_EQUAL( OtaErrNone, OTA_Resume() );

    /* Self test timer should be restarted if the device is self testing. */
    TEST_ASSERT_TRUE( bSelfTestTimerIsActive );
    TEST_ASSERT_TRUE( bRequestTimerIsActive );

    /* As this was a nominal flow, OTA should resume without issue. */
    receiveAndProcessOtaEvent();
    TEST_ASSERT_EQUAL( OtaAgentStateRequestingJob, OTA_GetState() );
}

void test_OTA_ResumeNoSelfTestTimerRestart()
{
    otaGoToState( OtaAgentStateSuspended );
    TEST_ASSERT_EQUAL( OtaAgentStateSuspended, OTA_GetState() );

    /* Reset timer state and configure mocked timer function for tracking timer state */
    bSelfTestTimerIsActive = false;
    bRequestTimerIsActive = false;
    otaInterfaces.os.timer.start = mockOSTimerStart;
    otaInterfaces.os.timer.stop = mockOSTimerStop;
    otaInterfaces.os.event.send = mockOSEventSend;

    /* Let the PAL always says it's not in self test. */
    otaInterfaces.pal.getPlatformImageState = mockPalGetPlatformImageStateAlwaysInvalid;
    TEST_ASSERT_EQUAL( OtaErrNone, OTA_Resume() );

    /* Self test timer should NOT be restarted if the device is not self testing. */
    TEST_ASSERT_FALSE( bSelfTestTimerIsActive );
    TEST_ASSERT_TRUE( bRequestTimerIsActive );

    /* As this was a nominal flow, OTA should resume without issue. */
    receiveAndProcessOtaEvent();
    TEST_ASSERT_EQUAL( OtaAgentStateRequestingJob, OTA_GetState() );
}

void test_OTA_Statistics()
{
    otaGoToState( OtaAgentStateReady );
    TEST_ASSERT_EQUAL( OtaAgentStateReady, OTA_GetState() );

    TEST_ASSERT_EQUAL( OtaErrInvalidArg, OTA_GetStatistics( NULL ) );

    OtaAgentStatistics_t statistics = { 0 };
    TEST_ASSERT_EQUAL( OtaErrNone, OTA_GetStatistics( &statistics ) );

    TEST_ASSERT_EQUAL( 0, statistics.otaPacketsReceived );
    TEST_ASSERT_EQUAL( 0, statistics.otaPacketsQueued );
    TEST_ASSERT_EQUAL( 0, statistics.otaPacketsProcessed );
    TEST_ASSERT_EQUAL( 0, statistics.otaPacketsDropped );
}

void test_OTA_CheckForUpdate()
{
    otaGoToState( OtaAgentStateRequestingJob );
    TEST_ASSERT_EQUAL( OtaAgentStateRequestingJob, OTA_GetState() );

    TEST_ASSERT_EQUAL( OtaErrNone, OTA_CheckForUpdate() );
    receiveAndProcessOtaEvent();
    TEST_ASSERT_EQUAL( OtaAgentStateWaitingForJob, OTA_GetState() );
}

void test_OTA_CheckForUpdateFailToSendEvent()
{
    otaGoToState( OtaAgentStateRequestingJob );
    TEST_ASSERT_EQUAL( OtaAgentStateRequestingJob, OTA_GetState() );

    /* Set the event send interface to a mock function that always fail. */
    otaInterfaces.os.event.send = mockOSEventSendAlwaysFail;

    /* Check for update should fail and OTA agent should remain in requesting job state. */
    TEST_ASSERT_EQUAL( OtaErrSignalEventFailed, OTA_CheckForUpdate() );
    TEST_ASSERT_EQUAL( OtaAgentStateRequestingJob, OTA_GetState() );
}

void test_OTA_ActivateNewImage()
{
    otaGoToState( OtaAgentStateReady );
    TEST_ASSERT_EQUAL( OtaAgentStateReady, OTA_GetState() );

    /* Activate image simply calls the PAL implementation and return its return value. */
    TEST_ASSERT_EQUAL( OtaErrNone, OTA_ActivateNewImage() );

    otaInterfaces.pal.activate = mockPalActivateReturnFail;
    TEST_ASSERT_EQUAL( OtaErrActivateFailed, OTA_ActivateNewImage() );
}

/* OTA pal function pointers should be NULL when OTA agent stopped. Calling OTA_ActivateNewImage
 * should fail. */
void test_OTA_ActivateNewImageWhenStopped()
{
    TEST_ASSERT_NOT_EQUAL( OtaErrActivateFailed, OTA_ActivateNewImage() );
}

void test_OTA_ActivateNewImageNullPalActivate()
{
    /* Have all other interfaces besides the activate function of the PAL
     * interface. */
    otaInterfaces.pal.activate = NULL;

    /* Initialize the OTA Agent to set the interfaces before trying to
     * activate the new image. */
    OTA_Init( &pOtaAppBuffer,
              &otaInterfaces,
              ( const uint8_t * ) pOtaDefaultClientId,
              mockAppCallback );

    TEST_ASSERT_EQUAL( OtaAgentStateInit, OTA_GetState() );
    TEST_ASSERT_EQUAL( OtaErrActivateFailed, OTA_ActivateNewImage() );
}

void test_OTA_ActivateNewImageNullOtaInterface()
{
    otaInitDefault();
    TEST_ASSERT_EQUAL( OtaAgentStateInit, OTA_GetState() );

    /* Set OTA interface to NULL. */
    otaAgent.pOtaInterface = NULL;

    TEST_ASSERT_EQUAL( OtaErrActivateFailed, OTA_ActivateNewImage() );

    /* Reset OTA interface. */
    otaAgent.pOtaInterface = &otaInterfaces;
}

void test_OTA_ImageStateAbortWithActiveJob()
{
    otaGoToState( OtaAgentStateWaitingForFileBlock );

    /* Calling abort with an active job would make OTA agent transit to waiting for job state. */
    TEST_ASSERT_EQUAL( OtaErrNone, OTA_SetImageState( OtaImageStateAborted ) );
    receiveAndProcessOtaEvent();
    TEST_ASSERT_EQUAL( OtaAgentStateWaitingForJob, OTA_GetState() );
}

void test_OTA_ImageStateAbortWithNoJob()
{
    otaGoToState( OtaAgentStateReady );
    TEST_ASSERT_EQUAL( OtaAgentStateReady, OTA_GetState() );

    /* Set the event send interface to a mock function that allows events to be sent continuously
     * since setting image state to abort would send an user abort event in the handler. */
    otaInterfaces.os.event.send = mockOSEventSend;

    /* Calling abort without an active job would fail. OTA agent should remain in ready state. */
    TEST_ASSERT_EQUAL( OtaErrNone, OTA_SetImageState( OtaImageStateAborted ) );
    receiveAndProcessOtaEvent();
    TEST_ASSERT_EQUAL( OtaAgentStateReady, OTA_GetState() );
}

void test_OTA_ImageStateAbortFailToSendEvent()
{
    otaGoToState( OtaAgentStateReady );
    TEST_ASSERT_EQUAL( OtaAgentStateReady, OTA_GetState() );

    /* Set the event send interface to a mock function that always fail. */
    otaInterfaces.os.event.send = mockOSEventSendAlwaysFail;

    TEST_ASSERT_EQUAL( OtaErrSignalEventFailed, OTA_SetImageState( OtaImageStateAborted ) );
    TEST_ASSERT_EQUAL( OtaAgentStateReady, OTA_GetState() );
}

void test_OTA_ImageStateAbortUpdateStatusFail()
{
    /* Allow event to be sent continuously so that retries can work. */
    otaInterfaces.os.event.send = mockOSEventSend;

    otaGoToState( OtaAgentStateWaitingForFileBlock );

    /* Successfully send the event to abort the image. */
    TEST_ASSERT_EQUAL( OtaErrNone, OTA_SetImageState( OtaImageStateAborted ) );

    /* Process the event to abort the image and fail to update the job status. */
    otaControlInterface.updateJobStatus = mockControlInterfaceUpdateJobAlwaysFail;
    receiveAndProcessOtaEvent();

    /* Test that the image state will be set regardless of whether or not the
     * job status was updated successfully. */
    TEST_ASSERT_EQUAL( OtaImageStateAborted, OTA_GetImageState() );
}

void test_OTA_ImageStateRjectWithActiveJob()
{
    otaGoToState( OtaAgentStateWaitingForFileBlock );

    TEST_ASSERT_EQUAL( OtaErrNone, OTA_SetImageState( OtaImageStateRejected ) );
    TEST_ASSERT_EQUAL( OtaImageStateRejected, OTA_GetImageState() );
}

void test_OTA_ImageStateRjectWithNoJob()
{
    otaGoToState( OtaAgentStateReady );
    TEST_ASSERT_EQUAL( OtaAgentStateReady, OTA_GetState() );

    TEST_ASSERT_EQUAL( OtaErrNoActiveJob, OTA_SetImageState( OtaImageStateRejected ) );
    TEST_ASSERT_EQUAL( OtaImageStateRejected, OTA_GetImageState() );
}

void test_OTA_ImageStateAcceptWithActiveJob()
{
    otaGoToState( OtaAgentStateWaitingForFileBlock );

    TEST_ASSERT_EQUAL( OtaErrNone, OTA_SetImageState( OtaImageStateAccepted ) );
    TEST_ASSERT_EQUAL( OtaImageStateAccepted, OTA_GetImageState() );
}

void test_OTA_ImageStateAcceptWithActiveJobNullAppCallback()
{
    otaInit( pOtaDefaultClientId, NULL );

    otaGoToState( OtaAgentStateWaitingForFileBlock );

    TEST_ASSERT_EQUAL( OtaErrNone, OTA_SetImageState( OtaImageStateAccepted ) );
    TEST_ASSERT_EQUAL( OtaImageStateAccepted, OTA_GetImageState() );
}

void test_OTA_ImageStateAcceptWithNoJob()
{
    otaGoToState( OtaAgentStateReady );
    TEST_ASSERT_EQUAL( OtaAgentStateReady, OTA_GetState() );

    TEST_ASSERT_EQUAL( OtaErrNoActiveJob, OTA_SetImageState( OtaImageStateAccepted ) );
    TEST_ASSERT_EQUAL( OtaImageStateAccepted, OTA_GetImageState() );
}

void test_OTA_ImageStateInvalidState()
{
    TEST_ASSERT_EQUAL( OtaErrInvalidArg, OTA_SetImageState( -1 ) );
}

void test_OTA_ImageStatePalFail()
{
    otaInterfaces.pal.setPlatformImageState = mockPalSetPlatformImageStateAlwaysFail;
    otaGoToState( OtaAgentStateReady );
    TEST_ASSERT_EQUAL( OtaErrNoActiveJob, OTA_SetImageState( OtaImageStateAccepted ) );
    TEST_ASSERT_EQUAL( OtaImageStateRejected, OTA_GetImageState() );
}

void test_OTA_ImageStateWithReasonPalFail()
{
    OtaImageState_t stateToSet = OtaImageStateAccepted;
    OtaErr_t error;

    otaGoToState( OtaAgentStateReady );
    otaInterfaces.pal.setPlatformImageState = mockPalSetPlatformImageStateAlwaysFail;
    error = setImageStateWithReason( stateToSet, OtaErrImageStateMismatch );
    TEST_ASSERT_EQUAL( OtaErrNoActiveJob, error );
}

void test_OTA_RequestJobDocumentRetryFail()
{
    OtaEventMsg_t otaEvent = { 0 };
    uint32_t i = 0;

    otaGoToState( OtaAgentStateReady );
    TEST_ASSERT_EQUAL( OtaAgentStateReady, OTA_GetState() );

    /* Let MQTT publish fail so request job will also fail. */
    otaInterfaces.mqtt.publish = stubMqttPublishAlwaysFail;

    /* Let timer invoke callback directly. */
    otaInterfaces.os.timer.start = mockOSTimerInvokeCallback;

    /* Allow event to be sent continuously so that retries can work. */
    otaInterfaces.os.event.send = mockOSEventSend;

    /* Place the OTA Agent into the state for requesting a job. */
    otaEvent.eventId = OtaAgentEventStart;
    OTA_SignalEvent( &otaEvent );
    receiveAndProcessOtaEvent();
    TEST_ASSERT_EQUAL( OtaAgentStateRequestingJob, OTA_GetState() );

    /* Fail the maximum number of attempts to request a job document. */
    for( i = 0U; i < otaconfigMAX_NUM_REQUEST_MOMENTUM; ++i )
    {
        receiveAndProcessOtaEvent();
        TEST_ASSERT_EQUAL( OtaAgentStateRequestingJob, OTA_GetState() );
    }

    /* Attempt to request another job document after failing the maximum number
     * of times, triggering a shutdown event. */
    receiveAndProcessOtaEvent();
    TEST_ASSERT_EQUAL( OtaAgentStateRequestingJob, OTA_GetState() );

    /* Shutdown after processing the shutdown event. */
    receiveAndProcessOtaEvent();
    TEST_ASSERT_EQUAL( OtaAgentStateStopped, OTA_GetState() );
}

void test_OTA_ProcessJobDocumentInvalidJson()
{
    pOtaJobDoc = JOB_DOC_INVALID;

    otaGoToState( OtaAgentStateWaitingForJob );
    TEST_ASSERT_EQUAL( OtaAgentStateWaitingForJob, OTA_GetState() );

    otaReceiveJobDocument();
    receiveAndProcessOtaEvent();
    TEST_ASSERT_EQUAL( OtaAgentStateWaitingForJob, OTA_GetState() );
}

/**
 * @brief Test that the job is rejected if the file key signature cannot be
 * decoded.
 */
void test_OTA_ProcessJobDocumentInvalidBase64Key()
{
    pOtaJobDoc = JOB_DOC_INVALID_BASE64_KEY;


    otaGoToState( OtaAgentStateWaitingForJob );
    TEST_ASSERT_EQUAL( OtaAgentStateWaitingForJob, OTA_GetState() );

    otaReceiveJobDocument();
    receiveAndProcessOtaEvent();
    TEST_ASSERT_EQUAL( OtaAgentStateWaitingForJob, OTA_GetState() );
}

/**
 * @brief Test that the job is rejected if a required key(here filesize)
 * is missing from the job document.
 */
void test_OTA_ProcessJobDocumentMissingRequiredKey()
{
    pOtaJobDoc = JOB_DOC_MISSING_KEY;

    otaGoToState( OtaAgentStateWaitingForJob );
    TEST_ASSERT_EQUAL( OtaAgentStateWaitingForJob, OTA_GetState() );

    otaReceiveJobDocument();
    receiveAndProcessOtaEvent();
    TEST_ASSERT_EQUAL( OtaAgentStateWaitingForJob, OTA_GetState() );
}

/**
 * @brief Test that the job is rejected if a field that is expected
 * to be an integer is NaN.
 */
void test_OTA_ProcessJobDocumentInvalidNum()
{
    pOtaJobDoc = JOB_DOC_INVALID_NUMBER_VAL;

    otaGoToState( OtaAgentStateWaitingForJob );
    TEST_ASSERT_EQUAL( OtaAgentStateWaitingForJob, OTA_GetState() );

    otaReceiveJobDocument();
    receiveAndProcessOtaEvent();
    TEST_ASSERT_EQUAL( OtaAgentStateWaitingForJob, OTA_GetState() );
}

/**
 * @brief Test that the job is rejected if a field that is expected
 * to be an integer is greater than the maximum allowed number for
 * string to int conversion (LONG_MAX).
 */
void test_OTA_ProcessJobDocumentNumOverflow()
{
    pOtaJobDoc = JOB_DOC_INVALID_NUMBER_NAN;

    otaGoToState( OtaAgentStateWaitingForJob );
    TEST_ASSERT_EQUAL( OtaAgentStateWaitingForJob, OTA_GetState() );

    otaReceiveJobDocument();
    receiveAndProcessOtaEvent();
    TEST_ASSERT_EQUAL( OtaAgentStateWaitingForJob, OTA_GetState() );
}

void test_OTA_ProcessCustomJobAppCallbackFails()
{
    pOtaJobDoc = JOB_DOC_MISSING_KEY;
    otaInit( pOtaDefaultClientId, mockAppCallbackCustomParsingFails );
    TEST_ASSERT_EQUAL( OtaAgentStateInit, OTA_GetState() );

    otaGoToState( OtaAgentStateCreatingFile );
    TEST_ASSERT_EQUAL( OtaAgentStateWaitingForJob, OTA_GetState() );
}

void test_OTA_ProcessCustomJobFailsInvalidKeys()
{
    /* Custom job parsing fails with key 'jobDocument' missing. */
    pOtaJobDoc = JOB_DOC_MISSING_JOB_DOC;
    otaGoToState( OtaAgentStateCreatingFile );
    TEST_ASSERT_EQUAL( OtaAgentStateWaitingForJob, OTA_GetState() );

    /* Custom job parsing fails with key 'jobId' missing. */
    pOtaJobDoc = JOB_DOC_MISSING_JOB_ID;
    otaGoToState( OtaAgentStateCreatingFile );
    TEST_ASSERT_EQUAL( OtaAgentStateWaitingForJob, OTA_GetState() );

    /* Custom job parsing fails with value of 'jobId' exceeding max length(72). */
    pOtaJobDoc = JOB_DOC_INVALID_JOB_ID;
    otaGoToState( OtaAgentStateCreatingFile );
    TEST_ASSERT_EQUAL( OtaAgentStateWaitingForJob, OTA_GetState() );
}

void test_OTA_RejectWhileAborted()
{
    pOtaJobDoc = JOB_DOC_INVALID;

    otaGoToState( OtaAgentStateWaitingForJob );
    TEST_ASSERT_EQUAL( OtaAgentStateWaitingForJob, OTA_GetState() );

    otaInterfaces.pal.setPlatformImageState = mockPalSetPlatformImageStateAlwaysFail;
    otaReceiveJobDocument();
    receiveAndProcessOtaEvent();

    /* Test that the OTA Agent is able to recover after failing to reject a job
     * due to already having aborted the job. It is not necessary for the call
     * to setPlatformImageState to fail for this behavior to happen, but it is
     * required to reach the branch that checks for this scenario. */
    TEST_ASSERT_EQUAL( OtaAgentStateWaitingForJob, OTA_GetState() );
}

void test_OTA_ProcessJobDocumentInvalidProtocol()
{
    pOtaJobDoc = JOB_DOC_INVALID_PROTOCOL;

    otaGoToState( OtaAgentStateWaitingForJob );
    TEST_ASSERT_EQUAL( OtaAgentStateWaitingForJob, OTA_GetState() );

    otaReceiveJobDocument();
    receiveAndProcessOtaEvent();
    TEST_ASSERT_EQUAL( OtaAgentStateCreatingFile, OTA_GetState() );
}

void test_OTA_ProcessJobDocumentInvalidProtocolPalFails()
{
    pOtaJobDoc = JOB_DOC_INVALID_PROTOCOL;
    otaInterfaces.pal.setPlatformImageState = mockPalSetPlatformImageStateAlwaysFail;

    otaGoToState( OtaAgentStateWaitingForJob );
    TEST_ASSERT_EQUAL( OtaAgentStateWaitingForJob, OTA_GetState() );

    otaReceiveJobDocument();
    receiveAndProcessOtaEvent();
    TEST_ASSERT_EQUAL( OtaAgentStateCreatingFile, OTA_GetState() );
}

void test_OTA_ProcessJobDocumentValidJson()
{
    pOtaJobDoc = JOB_DOC_A;

    otaGoToState( OtaAgentStateWaitingForJob );
    TEST_ASSERT_EQUAL( OtaAgentStateWaitingForJob, OTA_GetState() );

    otaReceiveJobDocument();
    receiveAndProcessOtaEvent();
    TEST_ASSERT_EQUAL( OtaAgentStateCreatingFile, OTA_GetState() );
}

void test_OTA_ProcessJobDocumentPalCreateFileFail()
{
    otaInterfaces.pal.createFile = mockPalCreateFileForRxAlwaysFail;

    otaGoToState( OtaAgentStateWaitingForJob );
    TEST_ASSERT_EQUAL( OtaAgentStateWaitingForJob, OTA_GetState() );

    otaReceiveJobDocument();
    receiveAndProcessOtaEvent();
    TEST_ASSERT_EQUAL( OtaAgentStateWaitingForJob, OTA_GetState() );
}

void test_OTA_ProcessJobDocumentBitmapMallocFail()
{
    pOtaAppBuffer.pFileBitmap = NULL;
    otaInterfaces.os.mem.malloc = mockMallocAlwaysFail;

    otaGoToState( OtaAgentStateWaitingForJob );
    TEST_ASSERT_EQUAL( OtaAgentStateWaitingForJob, OTA_GetState() );

    otaReceiveJobDocument();
    receiveAndProcessOtaEvent();
    TEST_ASSERT_EQUAL( OtaAgentStateWaitingForJob, OTA_GetState() );
}

void test_OTA_ProcessJobDocumentEventSendFail( void )
{
    pOtaJobDoc = JOB_DOC_A;

    otaGoToState( OtaAgentStateWaitingForJob );
    TEST_ASSERT_EQUAL( OtaAgentStateWaitingForJob, OTA_GetState() );

    otaReceiveJobDocument();

    otaInterfaces.os.event.send = mockOSEventSendAlwaysFail;
    receiveAndProcessOtaEvent();
    TEST_ASSERT_EQUAL( OtaAgentStateWaitingForJob, OTA_GetState() );
}

static void otaInitFileTransfer()
{
    OtaEventMsg_t otaEvent = { 0 };

    otaGoToState( OtaAgentStateCreatingFile );
    TEST_ASSERT_EQUAL( OtaAgentStateCreatingFile, OTA_GetState() );

    otaEvent.eventId = OtaAgentEventCreateFile;
    OTA_SignalEvent( &otaEvent );
    receiveAndProcessOtaEvent();
    TEST_ASSERT_EQUAL( OtaAgentStateRequestingFileBlock, OTA_GetState() );
}

void test_OTA_InitFileTransferMqtt()
{
    pOtaJobDoc = JOB_DOC_A;
    otaInitFileTransfer();
}

void test_OTA_InitFileTransferHttp()
{
    pOtaJobDoc = JOB_DOC_HTTP;
    otaInitFileTransfer();
}

void test_OTA_InitFileTransferRetryFail()
{
    uint32_t i = 0U;

    /* Use HTTP data transfer so we can intentionally fail the init transfer. */
    pOtaJobDoc = JOB_DOC_HTTP;

    otaGoToState( OtaAgentStateWaitingForJob );
    TEST_ASSERT_EQUAL( OtaAgentStateWaitingForJob, OTA_GetState() );

    /* Let http init fail so init file transfer will also fail. */
    otaInterfaces.http.init = mockHttpInitAlwaysFail;

    /* Let timer invoke callback directly. */
    otaInterfaces.os.timer.start = mockOSTimerInvokeCallback;

    /* Allow event to be sent continuously so that retries can work. */
    otaInterfaces.os.event.send = mockOSEventSend;

    /* After receiving a valid job document, OTA agent should first transit to creating file state.
     * Then keep calling init file transfer until failed, which should then shutdown itself. */
    otaReceiveJobDocument();
    receiveAndProcessOtaEvent();
    TEST_ASSERT_EQUAL( OtaAgentStateCreatingFile, OTA_GetState() );

    /* Make the maximum number of failures based on the momentum parameter. */
    for( i = 0U; i < otaconfigMAX_NUM_REQUEST_MOMENTUM; ++i )
    {
        receiveAndProcessOtaEvent();
        TEST_ASSERT_EQUAL( OtaAgentStateCreatingFile, OTA_GetState() );
    }

    /* Make another attempt after already reaching the maximum number of
     * allowable attempts, which generates a shutdown event. */
    receiveAndProcessOtaEvent();
    TEST_ASSERT_EQUAL( OtaAgentStateCreatingFile, OTA_GetState() );

    /* Shutdown the OTA Agent after processing the event. */
    receiveAndProcessOtaEvent();
    TEST_ASSERT_EQUAL( OtaAgentStateStopped, OTA_GetState() );
}

static void otaRequestFileBlock()
{
    OtaEventMsg_t otaEvent = { 0 };

    otaGoToState( OtaAgentStateRequestingFileBlock );
    TEST_ASSERT_EQUAL( OtaAgentStateRequestingFileBlock, OTA_GetState() );

    otaEvent.eventId = OtaAgentEventRequestFileBlock;
    OTA_SignalEvent( &otaEvent );
    receiveAndProcessOtaEvent();
    TEST_ASSERT_EQUAL( OtaAgentStateWaitingForFileBlock, OTA_GetState() );
}

void test_OTA_RequestFileBlockMqtt()
{
    pOtaJobDoc = JOB_DOC_A;
    otaRequestFileBlock();
}

void test_OTA_RequestFileBlockHttp()
{
    pOtaJobDoc = JOB_DOC_HTTP;
    otaRequestFileBlock();
}

void test_OTA_RequestFileBlockHttpOneBlock()
{
    pOtaJobDoc = JOB_DOC_ONE_BLOCK;
    otaRequestFileBlock();
}

void test_OTA_RequestFileBlockTimerFails()
{
    OtaEventMsg_t otaEvent = { 0 };

    /* Set the event send functionality to always succeed. */
    otaInterfaces.os.event.send = mockOSEventSend;

    /* Prepare the OTA Agent to request a block. */
    otaGoToState( OtaAgentStateRequestingFileBlock );
    TEST_ASSERT_EQUAL( OtaAgentStateRequestingFileBlock, OTA_GetState() );

    otaEvent.eventId = OtaAgentEventRequestFileBlock;
    OTA_SignalEvent( &otaEvent );

    /* Set the request timer to fail when attempting to start. */
    otaInterfaces.os.timer.start = mockOSTimerStartAlwaysFail;
    /* Process the event to request a block. */
    receiveAndProcessOtaEvent();
    /* Process the event to shut down. */
    receiveAndProcessOtaEvent();
    TEST_ASSERT_EQUAL( OtaAgentStateStopped, OTA_GetState() );
}

void test_OTA_RequestFileBlockRetryFail()
{
    uint32_t i = 0;

    /* Use HTTP data transfer so we can intentionally fail the file block request. */
    pOtaJobDoc = JOB_DOC_HTTP;

    otaGoToState( OtaAgentStateWaitingForJob );
    TEST_ASSERT_EQUAL( OtaAgentStateWaitingForJob, OTA_GetState() );

    /* Let http request fail so request file block will also fail. */
    otaInterfaces.http.request = mockHttpRequestAlwaysFail;

    /* Let timer invoke callback directly. */
    otaInterfaces.os.timer.start = mockOSTimerInvokeCallback;

    /* Allow event to be sent continuously so that retries can work. */
    otaInterfaces.os.event.send = mockOSEventSend;

    /* After receiving a valid job document and starts file transfer, OTA agent should first transit
     * to requesting file block state. Then keep calling request file block until failed. */

    /* Receive the job document. */
    otaReceiveJobDocument();
    receiveAndProcessOtaEvent();
    TEST_ASSERT_EQUAL( OtaAgentStateCreatingFile, OTA_GetState() );

    /* Successfully initialize the file transfer. */
    receiveAndProcessOtaEvent();
    TEST_ASSERT_EQUAL( OtaAgentStateRequestingFileBlock, OTA_GetState() );

    /* Request a file block and fail the maximum number of times. */
    for( i = 0; i < otaconfigMAX_NUM_REQUEST_MOMENTUM; ++i )
    {
        receiveAndProcessOtaEvent();
        TEST_ASSERT_EQUAL( OtaAgentStateRequestingFileBlock, OTA_GetState() );
    }

    /* The timer triggers as we check for the number of attempts so far. The
     * number of attempts is at the maximum already so we also create a
     * shutdown event. */
    receiveAndProcessOtaEvent();
    TEST_ASSERT_EQUAL( OtaAgentStateRequestingFileBlock, OTA_GetState() );

    /* Process the timer event. */
    receiveAndProcessOtaEvent();
    TEST_ASSERT_EQUAL( OtaAgentStateRequestingFileBlock, OTA_GetState() );

    /* Process the shutdown event. */
    receiveAndProcessOtaEvent();
    TEST_ASSERT_EQUAL( OtaAgentStateStopped, OTA_GetState() );
}

void test_OTA_ReceiveFileBlockEmpty()
{
    OtaEventMsg_t otaEvent = { 0 };

    otaGoToState( OtaAgentStateWaitingForFileBlock );
    TEST_ASSERT_EQUAL( OtaAgentStateWaitingForFileBlock, OTA_GetState() );

    /* Set the event send interface to a mock function that allows events to be sent continuously.
     * This is required because decode failure would cause OtaAgentEventCloseFile event to be sent
     * within the OTA event handler and we want it to be processed. */
    otaInterfaces.os.event.send = mockOSEventSend;

    otaEvent.eventId = OtaAgentEventReceivedFileBlock;
    otaEvent.pEventData = &eventBuffer;
    otaEvent.pEventData->dataLength = 0;
    OTA_SignalEvent( &otaEvent );
    /* Process the event for receiving the block to trigger digesting it. */
    receiveAndProcessOtaEvent();

    /* Process the event generated after failing to decode the block. The
     * expected result is that we close the file and begin waiting for a new
     * job document. */
    receiveAndProcessOtaEvent();
    TEST_ASSERT_EQUAL( OtaAgentStateWaitingForJob, OTA_GetState() );
}

void test_OTA_ReceiveFileBlockTooLarge()
{
    OtaEventMsg_t otaEvent = { 0 };

    pOtaJobDoc = JOB_DOC_HTTP;

    otaGoToState( OtaAgentStateWaitingForFileBlock );
    TEST_ASSERT_EQUAL( OtaAgentStateWaitingForFileBlock, OTA_GetState() );

    otaInterfaces.os.event.send = mockOSEventSend;

    otaEvent.eventId = OtaAgentEventReceivedFileBlock;
    otaEvent.pEventData = &eventBuffer;
    otaEvent.pEventData->dataLength = OTA_FILE_BLOCK_SIZE + 1;
    OTA_SignalEvent( &otaEvent );
    /* Process the event for receiving the block to trigger digesting it. */
    receiveAndProcessOtaEvent();
    /* Process the event generated after failing to decode the block. */
    receiveAndProcessOtaEvent();
    TEST_ASSERT_EQUAL( OtaAgentStateWaitingForJob, OTA_GetState() );
}

void test_OTA_ReceiveLastFileBlockTooSmall()
{
    OtaEventMsg_t otaEvent = { 0 };

    pOtaJobDoc = JOB_DOC_ONE_BLOCK;

    otaGoToState( OtaAgentStateWaitingForFileBlock );
    TEST_ASSERT_EQUAL( OtaAgentStateWaitingForFileBlock, OTA_GetState() );

    otaInterfaces.os.event.send = mockOSEventSend;

    otaEvent.eventId = OtaAgentEventReceivedFileBlock;
    otaEvent.pEventData = &eventBuffer;
    otaEvent.pEventData->dataLength = OTA_FILE_BLOCK_SIZE - 1;
    OTA_SignalEvent( &otaEvent );
    /* Process the event to receive the invalid block. */
    receiveAndProcessOtaEvent();
    /* Process the event generated after receiving an invalid block. */
    receiveAndProcessOtaEvent();
    TEST_ASSERT_EQUAL( OtaAgentStateWaitingForJob, OTA_GetState() );
}

void test_OTA_ReceiveWithNullFile()
{
    OtaEventMsg_t otaEvent = { 0 };
    const uint32_t dataSize = 1024;

    pOtaJobDoc = JOB_DOC_ONE_BLOCK;
    otaInterfaces.pal.createFile = mockPalCreateNullFileForRx;
    otaInterfaces.os.event.send = mockOSEventSend;

    otaGoToState( OtaAgentStateWaitingForFileBlock );
    TEST_ASSERT_EQUAL( OtaAgentStateWaitingForFileBlock, OTA_GetState() );

    otaEvent.eventId = OtaAgentEventReceivedFileBlock;
    otaEvent.pEventData = &eventBuffer;
    otaEvent.pEventData->dataLength = dataSize;
    OTA_SignalEvent( &otaEvent );
    /* Process the event to receive the block */
    receiveAndProcessOtaEvent();

    /* Process the event generated after receiving a valid block while the
     * Agent has a NULL file pointer. */
    receiveAndProcessOtaEvent();

    /* Having a NULL file pointer means that the data blocks can not be saved.
     * This is treated as a failure for the job as a whole. Ensure that after
     * failing the current job because the file pointer is NULL, the OTA Agent
     * goes back to the waiting for a job state. */
    TEST_ASSERT_EQUAL( OtaAgentStateWaitingForJob, OTA_GetState() );
}

void test_OTA_ReceiveWriteBlockFail()
{
    OtaEventMsg_t otaEvent = { 0 };
    const uint32_t dataSize = 1024;

    pOtaJobDoc = JOB_DOC_ONE_BLOCK;
    otaInterfaces.pal.writeBlock = mockPalWriteBlockAlwaysFail;

    otaGoToState( OtaAgentStateWaitingForFileBlock );
    TEST_ASSERT_EQUAL( OtaAgentStateWaitingForFileBlock, OTA_GetState() );

    otaInterfaces.os.event.send = mockOSEventSend;

    otaEvent.eventId = OtaAgentEventReceivedFileBlock;
    otaEvent.pEventData = &eventBuffer;
    otaEvent.pEventData->dataLength = dataSize;
    OTA_SignalEvent( &otaEvent );
    /* Process the event to receive the invalid block. */
    receiveAndProcessOtaEvent();
    /* Process the event generated after receiving an invalid block. */
    receiveAndProcessOtaEvent();
    TEST_ASSERT_EQUAL( OtaAgentStateWaitingForJob, OTA_GetState() );
}

void test_OTA_ReceiveWritePartialBlockFail()
{
    OtaEventMsg_t otaEvent = { 0 };
    const uint32_t dataSize = 1024;

    pOtaJobDoc = JOB_DOC_ONE_BLOCK;
    otaInterfaces.pal.writeBlock = mockPalWriteBlockPartialWrite;

    otaGoToState( OtaAgentStateWaitingForFileBlock );
    TEST_ASSERT_EQUAL( OtaAgentStateWaitingForFileBlock, OTA_GetState() );

    otaInterfaces.os.event.send = mockOSEventSend;

    otaEvent.eventId = OtaAgentEventReceivedFileBlock;
    otaEvent.pEventData = &eventBuffer;
    otaEvent.pEventData->dataLength = dataSize;
    OTA_SignalEvent( &otaEvent );
    /* Process the event to receive the invalid block. */
    receiveAndProcessOtaEvent();
    /* Process the event generated after receiving an invalid block. */
    receiveAndProcessOtaEvent();
    TEST_ASSERT_EQUAL( OtaAgentStateWaitingForJob, OTA_GetState() );
}

void test_OTA_ReceiveFileBlockCompleteMqtt()
{
    OtaEventMsg_t otaEvent;
    OtaEventData_t eventBuffers[ OTA_TEST_FILE_NUM_BLOCKS * OTA_TEST_DUPLICATE_NUM_BLOCKS ];
    uint8_t pFileBlock[ OTA_FILE_BLOCK_SIZE ] = { 0 };
    uint8_t pStreamingMessage[ OTA_FILE_BLOCK_SIZE * 2 ] = { 0 };
    size_t streamingMessageSize = 0;
    int remainingBytes = OTA_TEST_FILE_SIZE;
    int idx = 0;
    int dupIdx = 0;

    otaGoToState( OtaAgentStateWaitingForFileBlock );
    TEST_ASSERT_EQUAL( OtaAgentStateWaitingForFileBlock, OTA_GetState() );

    /* Set the event send interface to a mock function that allows events to be sent continuously
     * because we're receiving multiple blocks in this test. */
    otaInterfaces.os.event.send = mockOSEventSend;

    /* Fill the file block. */
    for( idx = 0; idx < ( int ) sizeof( pFileBlock ); idx++ )
    {
        pFileBlock[ idx ] = idx % UINT8_MAX;
    }

    /* Send blocks. */
    idx = 0;

    while( remainingBytes >= 0 )
    {
        /* Intentionally send duplicate blocks to test if we are handling it correctly. */
        for( dupIdx = 0; dupIdx < OTA_TEST_DUPLICATE_NUM_BLOCKS; dupIdx++ )
        {
            /* Construct a AWS IoT streaming message. */
            createOtaStreamingMessage(
                pStreamingMessage,
                sizeof( pStreamingMessage ),
                idx,
                pFileBlock,
                min( ( uint32_t ) remainingBytes, OTA_FILE_BLOCK_SIZE ),
                &streamingMessageSize,
                true );

            otaEvent.eventId = OtaAgentEventReceivedFileBlock;
            otaEvent.pEventData = &eventBuffers[ idx * OTA_TEST_DUPLICATE_NUM_BLOCKS + dupIdx ];
            memcpy( otaEvent.pEventData->data, pStreamingMessage, streamingMessageSize );
            otaEvent.pEventData->dataLength = streamingMessageSize;
            OTA_SignalEvent( &otaEvent );
        }

        idx++;
        remainingBytes -= OTA_FILE_BLOCK_SIZE;
    }

    /* Process all of the events for receiving an MQTT message. */
    processEntireQueue();
    /* OTA agent should complete the update and go back to waiting for job state. */
    receiveAndProcessOtaEvent();
    TEST_ASSERT_EQUAL( OtaAgentStateWaitingForJob, OTA_GetState() );

    /* Check if received complete file. */
    for( idx = 0; idx < OTA_TEST_FILE_SIZE; ++idx )
    {
        TEST_ASSERT_EQUAL( pFileBlock[ idx % sizeof( pFileBlock ) ], pOtaFileBuffer[ idx ] );
    }
}

void test_OTA_ReceiveFileBlockCompleteDynamicBufferMqtt()
{
    memset( &pOtaAppBuffer, 0, sizeof( pOtaAppBuffer ) );
    test_OTA_ReceiveFileBlockCompleteMqtt();
}

void test_OTA_ReceiveFileBlockCompleteDifferentFileTypeMqtt()
{
    pOtaJobDoc = JOB_DOC_DIFFERENT_FILE_TYPE;
    test_OTA_ReceiveFileBlockCompleteMqtt();
}

void test_OTA_ReceiveFileBlockMallocFail()
{
    uint8_t pStreamingMessage[ OTA_FILE_BLOCK_SIZE * 2 ] = { 0 };
    uint8_t pFileBlock[ OTA_FILE_BLOCK_SIZE ] = { 0 };
    size_t streamingMessageSize = 0;
    OtaEventData_t eventBuffer;
    OtaEventMsg_t otaEvent = { 0 };

    otaInterfaces.os.event.send = mockOSEventSend;

    /* Pass an invalid values for pDecodeMemory and decodeMemorySize so the
     * OTA Agent dynamically allocates the buffer instead of using one provided
     * by the user. */
    pOtaAppBuffer.pDecodeMemory = NULL;
    pOtaAppBuffer.decodeMemorySize = 0;

    /* Get into the state before receiving a data block. */
    otaGoToState( OtaAgentStateWaitingForFileBlock );
    TEST_ASSERT_EQUAL( OtaAgentStateWaitingForFileBlock, OTA_GetState() );

    /* Create and send the data block. */
    createOtaStreamingMessage(
        pStreamingMessage,
        sizeof( pStreamingMessage ),
        0,
        pFileBlock,
        OTA_FILE_BLOCK_SIZE,
        &streamingMessageSize,
        true );

    otaEvent.eventId = OtaAgentEventReceivedFileBlock;
    otaEvent.pEventData = &eventBuffer;
    memcpy( otaEvent.pEventData->data, pStreamingMessage, streamingMessageSize );
    otaEvent.pEventData->dataLength = streamingMessageSize;
    OTA_SignalEvent( &otaEvent );

    /* Set malloc to fail and receive the block. */
    otaInterfaces.os.mem.malloc = mockMallocAlwaysFail;
    receiveAndProcessOtaEvent();
    /* Receive the event for closing the file after the failure. */
    receiveAndProcessOtaEvent();
    TEST_ASSERT_EQUAL( OtaAgentStateWaitingForJob, OTA_GetState() );
}

void test_OTA_DroppedFileBlock()
{
    OtaEventMsg_t otaEvent = { 0 };

    otaInterfaces.os.event.send = mockOSEventSend;

    /* Get ready to receive a block. */
    otaGoToState( OtaAgentStateWaitingForFileBlock );
    TEST_ASSERT_EQUAL( OtaAgentStateWaitingForFileBlock, OTA_GetState() );
    /* No blocks have been received or dropped yet. */
    TEST_ASSERT_EQUAL( 0, otaAgent.statistics.otaPacketsDropped );


    /* Prepare an event as if we are receiving a data block. */
    otaEvent.eventId = OtaAgentEventReceivedFileBlock;
    otaEvent.pEventData = &eventBuffer;
    otaEvent.pEventData->dataLength = 0;

    /* Set the interface to fail sending the data block. */
    otaInterfaces.os.event.send = mockOSEventSendAlwaysFail;

    /* Simulate the application receiving a data block and failing to send it
     * to the OTA Agent. */
    TEST_ASSERT_EQUAL( false, OTA_SignalEvent( &otaEvent ) );
    TEST_ASSERT_EQUAL( 1, otaAgent.statistics.otaPacketsDropped );
    TEST_ASSERT_EQUAL( OtaAgentStateWaitingForFileBlock, OTA_GetState() );
}

void test_OTA_ReceiveFileBlockCompleteHttp()
{
    OtaEventMsg_t otaEvent;
    OtaEventData_t eventBuffers[ OTA_TEST_FILE_NUM_BLOCKS ];
    uint8_t pFileBlock[ OTA_FILE_BLOCK_SIZE ] = { 0 };
    int remainingBytes = OTA_TEST_FILE_SIZE;
    int fileBlockSize = 0;
    int idx = 0;

    pOtaJobDoc = JOB_DOC_HTTP;
    otaGoToState( OtaAgentStateWaitingForFileBlock );
    TEST_ASSERT_EQUAL( OtaAgentStateWaitingForFileBlock, OTA_GetState() );

    /* Set the event send interface to a mock function that allows events to be sent continuously
     * because we're receiving multiple blocks in this test. */
    otaInterfaces.os.event.send = mockOSEventSend;

    /* Fill the file block. */
    for( idx = 0; idx < ( int ) sizeof( pFileBlock ); idx++ )
    {
        pFileBlock[ idx ] = idx % UINT8_MAX;
    }

    idx = 0;

    while( remainingBytes >= 0 )
    {
        fileBlockSize = min( ( uint32_t ) remainingBytes, OTA_FILE_BLOCK_SIZE );
        otaEvent.eventId = OtaAgentEventReceivedFileBlock;
        otaEvent.pEventData = &eventBuffers[ idx ];
        memcpy( otaEvent.pEventData->data, pFileBlock, fileBlockSize );
        otaEvent.pEventData->dataLength = fileBlockSize;
        OTA_SignalEvent( &otaEvent );

        idx++;
        remainingBytes -= OTA_FILE_BLOCK_SIZE;
    }

    /* OTA agent should complete the update and go back to waiting for job state. */
    processEntireQueue();
    TEST_ASSERT_EQUAL( OtaAgentStateWaitingForJob, OTA_GetState() );

    /* Check if received complete file. */
    for( idx = 0; idx < OTA_TEST_FILE_SIZE; ++idx )
    {
        TEST_ASSERT_EQUAL( pFileBlock[ idx % sizeof( pFileBlock ) ], pOtaFileBuffer[ idx ] );
    }
}

void test_OTA_ReceiveFileBlockCompleteDynamicBufferHttp()
{
    memset( &pOtaAppBuffer, 0, sizeof( pOtaAppBuffer ) );
    test_OTA_ReceiveFileBlockCompleteHttp();
}

/**
 * @brief Test that extractAndStoreArray fails if device does not have sufficient
 * memory to allocate the string/array (here streamname).
 */
void test_OTA_ExtractArrayMemAllocFails()
{
    otaInterfaces.os.mem.malloc = mockMallocAlwaysFail;
    pOtaAppBuffer.streamNameSize = 0;

    /* Try to reach state OtaAgentStateCreatingFile, which would require the device
     * to receive a job document and allocate resources and store the parameters.
     * Insufficient memory causes the job to fail and state reverts to  OtaAgentStateWaitingForJob.
     */
    otaGoToState( OtaAgentStateCreatingFile );
    TEST_ASSERT_EQUAL( OtaAgentStateWaitingForJob, OTA_GetState() );
}

/**
 * @brief Test that extractAndStoreArray fails if user buffer is insufficient
 * to allocate the string/array (here streamname).
 */
void test_OTA_ExtractArrayInsufficientBuffer()
{
    pOtaAppBuffer.streamNameSize = OTA_INVALID_STREAM_NAME_SIZE;

    /* Try to reach state OtaAgentStateCreatingFile, which would require the device
     * to receive a job document and allocate resources and store the parameters.
     * Insufficient memory causes the job to fail and state reverts to  OtaAgentStateWaitingForJob.
     */
    otaGoToState( OtaAgentStateCreatingFile );
    TEST_ASSERT_EQUAL( OtaAgentStateWaitingForJob, OTA_GetState() );
}


void test_OTA_ProcessJobDocumentFileIdNotZero()
{
    pOtaJobDoc = JOB_DOC_SERVERFILE_ID;

    /* Set the event send interface to a mock function that allows events to be sent continuously.
     * This is to complete the self test process. */
    otaInterfaces.os.event.send = mockOSEventSend;

    otaGoToState( OtaAgentStateWaitingForJob );
    TEST_ASSERT_EQUAL( OtaAgentStateWaitingForJob, OTA_GetState() );

    otaReceiveJobDocument();
    receiveAndProcessOtaEvent();
    receiveAndProcessOtaEvent();
    TEST_ASSERT_EQUAL( OtaAgentStateWaitingForJob, OTA_GetState() );
    TEST_ASSERT_EQUAL( OtaImageStateAccepted, OTA_GetImageState() );
}

static void invokeSelfTestHandler()
{
    pOtaJobDoc = JOB_DOC_SELF_TEST;

    /* Set the event send interface to a mock function that allows events to be sent continuously.
     * This is to complete the self test process. */
    otaInterfaces.os.event.send = mockOSEventSend;

    otaGoToState( OtaAgentStateWaitingForJob );
    TEST_ASSERT_EQUAL( OtaAgentStateWaitingForJob, OTA_GetState() );

    otaReceiveJobDocument();
    receiveAndProcessOtaEvent();
    receiveAndProcessOtaEvent();
}

void test_OTA_SelfTestJob()
{
    invokeSelfTestHandler();
    TEST_ASSERT_EQUAL( OtaAgentStateWaitingForJob, OTA_GetState() );
    TEST_ASSERT_EQUAL( OtaImageStateAccepted, OTA_GetImageState() );
}

void test_OTA_SelfTestJobEventSendFail()
{
    pOtaJobDoc = JOB_DOC_SELF_TEST;

    otaGoToState( OtaAgentStateWaitingForJob );
    TEST_ASSERT_EQUAL( OtaAgentStateWaitingForJob, OTA_GetState() );

    /* Set the event send interface to a mock function that always fails to
     * send the event. */
    otaReceiveJobDocument();
    otaInterfaces.os.event.send = mockOSEventSendAlwaysFail;

    receiveAndProcessOtaEvent();
    TEST_ASSERT_EQUAL( OtaAgentStateWaitingForJob, OTA_GetState() );
}

void test_OTA_SelfTestJobNonSelfTestPlatform()
{
    /* Let the PAL always says it's not in self test. */
    otaInterfaces.pal.getPlatformImageState = mockPalGetPlatformImageStateAlwaysInvalid;

    invokeSelfTestHandler();
    TEST_ASSERT_EQUAL( OtaAgentStateWaitingForJob, OTA_GetState() );
    TEST_ASSERT_EQUAL( OtaImageStateRejected, OTA_GetImageState() );
}

void test_OTA_NonSelfTestJobSelfTestPlatform()
{
    /* Let the PAL always says it's in self test. */
    otaInterfaces.pal.getPlatformImageState = mockPalGetPlatformImageStateAlwaysPendingCommit;

    otaGoToState( OtaAgentStateCreatingFile );
    TEST_ASSERT_EQUAL( OtaAgentStateCreatingFile, OTA_GetState() );
}

void test_OTA_SelfTestJobDowngrade()
{
    pOtaJobDoc = JOB_DOC_SELF_TEST_DOWNGRADE;

    otaGoToState( OtaAgentStateWaitingForJob );
    TEST_ASSERT_EQUAL( OtaAgentStateWaitingForJob, OTA_GetState() );

    otaReceiveJobDocument();
    receiveAndProcessOtaEvent();
    TEST_ASSERT_EQUAL( true, resetCalled );
}

void test_OTA_SelfTestJobSameVersion()
{
    pOtaJobDoc = JOB_DOC_SELF_TEST_SAME_VERSION;

    otaGoToState( OtaAgentStateWaitingForJob );
    TEST_ASSERT_EQUAL( OtaAgentStateWaitingForJob, OTA_GetState() );

    otaReceiveJobDocument();
    receiveAndProcessOtaEvent();
    TEST_ASSERT_EQUAL( true, resetCalled );
}

void test_OTA_SelfTestJobNonFirmwareFileType()
{
    pOtaJobDoc = JOB_DOC_SELF_TEST_FILE_TYPE;
    otaInterfaces.os.event.send = mockOSEventSend;

    otaGoToState( OtaAgentStateWaitingForJob );
    TEST_ASSERT_EQUAL( OtaAgentStateWaitingForJob, OTA_GetState() );

    otaReceiveJobDocument();
    receiveAndProcessOtaEvent();
    receiveAndProcessOtaEvent();
    TEST_ASSERT_EQUAL( OtaAgentStateWaitingForJob, OTA_GetState() );
    TEST_ASSERT_EQUAL( OtaImageStateAccepted, OTA_GetImageState() );
}

void test_OTA_StartWithSelfTest()
{
    /* Directly set pal image state to pending commit, pretending we're in self test. */
    palImageState = OtaPalImageStatePendingCommit;

    /* Let timer start to invoke callback directly. */
    otaInterfaces.os.timer.start = mockOSTimerInvokeCallback;

    /* Start OTA agent. */
    otaGoToState( OtaAgentStateWaitingForJob );
    TEST_ASSERT_EQUAL( OtaAgentStateWaitingForJob, OTA_GetState() );
    TEST_ASSERT_EQUAL( true, resetCalled );
}

void test_OTA_ReceiveNewJobDocWhileInProgress()
{
    pOtaJobDoc = JOB_DOC_A;

    otaGoToState( OtaAgentStateWaitingForFileBlock );
    TEST_ASSERT_EQUAL( OtaAgentStateWaitingForFileBlock, OTA_GetState() );

    /* Reset the event queue so that we can send the next event. */
    mockOSEventReset( NULL );

    /* Sending another job document should cause OTA agent to abort current update. */
    pOtaJobDoc = JOB_DOC_B;
    otaReceiveJobDocument();
    receiveAndProcessOtaEvent();
    TEST_ASSERT_EQUAL( OtaAgentStateRequestingJob, OTA_GetState() );
}

static void refreshWithJobDoc( const char * initJobDoc,
                               const char * newJobDoc )
{
    OtaEventMsg_t otaEvent = { 0 };

    pOtaJobDoc = initJobDoc;

    otaGoToState( OtaAgentStateWaitingForFileBlock );
    TEST_ASSERT_EQUAL( OtaAgentStateWaitingForFileBlock, OTA_GetState() );

    /* Set the event send interface to a mock function that allows events to be sent continuously.
     * We need this to go through the process of refreshing job doc. */
    otaInterfaces.os.event.send = mockOSEventSend;

    /* First send request job doc event while we're in progress, this should make OTA agent to
     * to request job doc again and transit to waiting for job state. */
    otaEvent.eventId = OtaAgentEventRequestJobDocument;
    OTA_SignalEvent( &otaEvent );
    receiveAndProcessOtaEvent();
    TEST_ASSERT_EQUAL( OtaAgentStateWaitingForJob, OTA_GetState() );

    /* Now send the new job doc, OTA agent should abort current job and start the new job. */
    pOtaJobDoc = newJobDoc;
    otaReceiveJobDocument();
    receiveAndProcessOtaEvent();
    TEST_ASSERT_EQUAL( OtaAgentStateCreatingFile, OTA_GetState() );

    /* Request file block. */
    receiveAndProcessOtaEvent();
    TEST_ASSERT_EQUAL( OtaAgentStateRequestingFileBlock, OTA_GetState() );

    /* Wait for the file block. */
    receiveAndProcessOtaEvent();
    TEST_ASSERT_EQUAL( OtaAgentStateWaitingForFileBlock, OTA_GetState() );
}

void test_OTA_RefreshWithSameJobDoc()
{
    refreshWithJobDoc( JOB_DOC_A, JOB_DOC_A );
}

void test_OTA_RefreshWithInvalidJobDoc()
{
    OtaEventMsg_t otaEvent = { 0 };

    pOtaJobDoc = JOB_DOC_A;

    otaGoToState( OtaAgentStateWaitingForFileBlock );
    TEST_ASSERT_EQUAL( OtaAgentStateWaitingForFileBlock, OTA_GetState() );

    /* Set the event send interface to a mock function that allows events to be sent continuously.
     * We need this to go through the process of refreshing job doc. */
    otaInterfaces.os.event.send = mockOSEventSend;

    /* Send the request job document event while the OTA Agent is already in the process of
     * downloading a file. The OTA Agent should cancel the current job and begin waiting
     * for the next job document. */
    otaEvent.eventId = OtaAgentEventRequestJobDocument;
    OTA_SignalEvent( &otaEvent );
    receiveAndProcessOtaEvent();
    TEST_ASSERT_EQUAL( OtaAgentStateWaitingForJob, OTA_GetState() );

    /* Now send the new job doc, OTA agent should abort current job and start the new job. */
    pOtaJobDoc = JOB_DOC_MISSING_KEY;
    otaReceiveJobDocument();
    receiveAndProcessOtaEvent();
    TEST_ASSERT_EQUAL( OtaAgentStateWaitingForJob, OTA_GetState() );
}

void test_OTA_RefreshWithDifferentJobDoc()
{
    refreshWithJobDoc( JOB_DOC_A, JOB_DOC_B );
}

void test_OTA_RefreshWithSameJobDocHttpDynamicBuffer()
{
    memset( &pOtaAppBuffer, 0, sizeof( pOtaAppBuffer ) );
    refreshWithJobDoc( JOB_DOC_HTTP, JOB_DOC_HTTP );
}

void test_OTA_UnexpectedEventReceiveJobDoc()
{
    OtaEventMsg_t otaEvent = { 0 };

    otaGoToState( OtaAgentStateSuspended );
    TEST_ASSERT_EQUAL( OtaAgentStateSuspended, OTA_GetState() );

    otaEvent.eventId = OtaAgentEventReceivedJobDocument;
    OTA_SignalEvent( &otaEvent );

    receiveAndProcessOtaEvent();
    TEST_ASSERT_EQUAL( OtaAgentStateSuspended, OTA_GetState() );
}

void test_OTA_UnexpectedEventReceiveFileBlock()
{
    OtaEventMsg_t otaEvent = { 0 };

    otaGoToState( OtaAgentStateSuspended );
    TEST_ASSERT_EQUAL( OtaAgentStateSuspended, OTA_GetState() );

    otaEvent.eventId = OtaAgentEventReceivedFileBlock;
    OTA_SignalEvent( &otaEvent );

    receiveAndProcessOtaEvent();
    TEST_ASSERT_EQUAL( OtaAgentStateSuspended, OTA_GetState() );
}

void test_OTA_UnexpectedEventOthers()
{
    OtaEventMsg_t otaEvent = { 0 };

    otaGoToState( OtaAgentStateSuspended );
    TEST_ASSERT_EQUAL( OtaAgentStateSuspended, OTA_GetState() );

    otaEvent.eventId = OtaAgentEventStart;
    OTA_SignalEvent( &otaEvent );

    receiveAndProcessOtaEvent();
    TEST_ASSERT_EQUAL( OtaAgentStateSuspended, OTA_GetState() );
}

void test_OTA_ReceiveFileBlockCompleteMqttSigCheckFail()
{
    otaInterfaces.pal.closeFile = mockPalCloseFileSigCheckFail;
    test_OTA_ReceiveFileBlockCompleteMqtt();
}

void test_OTA_ReceiveFileBlockCompleteMqttFailtoClose()
{
    otaInterfaces.pal.closeFile = mockPalCloseFileAlwaysFail;
    test_OTA_ReceiveFileBlockCompleteMqtt();
}

void test_OTA_ReceiveFileBlockCompleteMqttCountUpdateJobCalledTime()
{
    otaGoToState( OtaAgentStateWaitingForFileBlock );

    otaControlInterface.updateJobStatus = mockControlInterfaceUpdateJobCount;
    test_OTA_ReceiveFileBlockCompleteMqtt();

    TEST_ASSERT_EQUAL( OTA_TEST_FILE_NUM_BLOCKS, otaReceivedFileBlockNumber );
}

void test_OTA_EventProcessingTask_ExitOnAbort()
{
    OtaEventMsg_t otaEvent = { 0 };

    otaGoToState( OtaAgentStateReady );
    otaEvent.eventId = OtaAgentEventShutdown;
    OTA_SignalEvent( &otaEvent );
    OTA_EventProcessingTask( NULL );

    /* Test that the OTA_EventProcessingTask aborts correctly after receiving
     * and event to shutdown the OTA Agent. */
    TEST_ASSERT_EQUAL( OtaAgentStateStopped, OTA_GetState() );

    /* Run OTA_EventProcessingTask again and OTA state should keep in OtaAgentStateStopped. */
    OTA_EventProcessingTask( NULL );

    TEST_ASSERT_EQUAL( OtaAgentStateStopped, OTA_GetState() );
}

void test_OTA_EventProcess_WhileNotStopped()
{
    OtaEventMsg_t otaEvent = { 0 };

    otaGoToState( OtaAgentStateReady );
    otaInterfaces.os.event.send = mockOSEventSend;

    /* Shutting down agent should stop OTA agent */
    otaEvent.eventId = OtaAgentEventShutdown;
    OTA_SignalEvent( &otaEvent );

    TEST_ASSERT_EQUAL( OtaAgentStateStopped, OTA_EventProcess() );
}

void test_OTA_EventProcess_WhileStopped()
{
    /* Reset to known state */
    OtaEventMsg_t otaEvent = { 0 };
    OtaEventMsg_t * ulQueueEndBefore = NULL;

    otaGoToState( OtaAgentStateStopped );

    /*  Mimic the agent state as though it was shutdown after running */
    otaInterfaces.os.event.send = mockOSEventSend;
    otaAgent.pOtaInterface = &otaInterfaces;

    /* Agent is stopped so event should not be processed and user callbacks/functions should not be exercised. */
    otaEvent.eventId = OtaAgentEventReceivedJobDocument;
    OTA_SignalEvent( &otaEvent );
    ulQueueEndBefore = otaEventQueueEnd;
    TEST_ASSERT_EQUAL( OtaAgentStateStopped, OTA_EventProcess() );
    TEST_ASSERT_EQUAL( otaEventQueueEnd, ulQueueEndBefore );
}

void test_OTA_EventProcess_AgentUpdatesReadiness()
{
    /* Reset to known state */
    otaInterfaces.os.event.send = mockOSEventSend;
    otaGoToState( OtaAgentStateStopped );

    /* Internally calls OTA_Init which will set state to initialized state, which will allow
     * OTA_EventProcess to set state to OtaAgentStateReady */
    otaInitDefault();
    TEST_ASSERT_EQUAL( OtaAgentStateInit, OTA_GetState() );

    /* Calling Event Process should once should put agent into ready state,
     * and update agent to indicate readiness */
    TEST_ASSERT_EQUAL( OtaAgentStateReady, OTA_EventProcess() );
}



/* ========================================================================== */
/* ====================== OTA MQTT and HTTP Unit Tests ====================== */
/* ========================================================================== */

/* Test that mqtt cleanup fails with unsubscribe failure. */
void test_OTA_MQTT_CleanupFailed()
{
    OtaEventMsg_t otaEvent = { 0 };

    otaAgent.unsubscribeOnShutdown = 1;

    otaGoToState( OtaAgentStateRequestingJob );
    TEST_ASSERT_EQUAL( OtaAgentStateRequestingJob, OTA_GetState() );

    otaInterfaces.mqtt.unsubscribe = stubMqttUnsubscribeAlwaysFail;

    otaEvent.eventId = OtaAgentEventShutdown;
    OTA_SignalEvent( &otaEvent );
    receiveAndProcessOtaEvent();
    TEST_ASSERT_EQUAL( OtaAgentStateStopped, OTA_GetState() );
}

/* Test that requestFileBlock_Mqtt fails if the Encoding fails. */
void test_OTA_MQTT_EncodingFailed()
{
    OtaErr_t err = OtaErrNone;

    otaInitDefault();

    /* Explicitly set BitMap to NULL for the encoding to fail. */
    OtaFileContext_t * pFileContext = &( otaAgent.fileContext );

    pFileContext->pRxBlockBitmap = NULL;

    err = requestFileBlock_Mqtt( &otaAgent );
    TEST_ASSERT_EQUAL( OtaErrFailedToEncodeCbor, err );
}

/* Test that requestFileBlock_Mqtt fails if the Publish fails. */
void test_OTA_MQTT_RequestFileFailed()
{
    OtaErr_t err = OtaErrNone;

    otaInitDefault();
    otaInterfaces.mqtt.publish = stubMqttPublishAlwaysFail;
    err = requestFileBlock_Mqtt( &otaAgent );
    TEST_ASSERT_EQUAL( OtaErrRequestFileBlockFailed, err );
}

/* Test that requestJob_Mqtt fails if the Subscribe fails. */
void test_OTA_MQTT_JobSubscribingFailed()
{
    OtaErr_t err = OtaErrNone;

    otaInitDefault();
    otaInterfaces.mqtt.subscribe = stubMqttSubscribeAlwaysFail;
    err = requestJob_Mqtt( &otaAgent );
    TEST_ASSERT_EQUAL( OtaErrRequestJobFailed, err );
}

/* Test that initFileTransfer_Mqtt fails if the Subscribe fails. */
void test_OTA_MQTT_InitFileTransferSubscribeFailed()
{
    OtaErr_t err = OtaErrNone;

    otaInitDefault();
    otaInterfaces.mqtt.subscribe = stubMqttSubscribeAlwaysFail;
    err = initFileTransfer_Mqtt( &otaAgent );
    TEST_ASSERT_EQUAL( OtaErrInitFileTransferFailed, err );
}

/* Test that updateJobStatus_Mqtt fails if the Publish fails. */
void test_OTA_MQTT_UpdateStatusFailed()
{
    OtaErr_t err = OtaErrNone;

    otaInitDefault();
    otaInterfaces.mqtt.publish = stubMqttPublishAlwaysFail;
    err = updateJobStatus_Mqtt( &otaAgent, JobStatusSucceeded, 0, 0 );
    TEST_ASSERT_EQUAL( OtaErrUpdateJobStatusFailed, err );
}

/* Test data cleanup fails with HTTP deinit failure*/
void test_OTA_HTTP_cleanupFailed()
{
    OtaErr_t err = OtaErrNone;

    otaInitDefault();
    otaInterfaces.http.deinit = stubHttpDeinitAlwaysFail;
    err = cleanupData_Http( &otaAgent );
    TEST_ASSERT_EQUAL( OtaErrCleanupDataFailed, err );
}

/* ========================================================================== */
/* ======================= OTA StrError Unit Tests ========================== */
/* ========================================================================== */

/**
 * @brief Test OTA_Err_strerror returns correct strings.
 */
void test_OTA_Err_strerror( void )
{
    OtaErr_t err;
    const char * str = NULL;

    err = OtaErrNone;
    str = OTA_Err_strerror( err );
    TEST_ASSERT_EQUAL_STRING( "OtaErrNone", str );
    err = OtaErrUninitialized;
    str = OTA_Err_strerror( err );
    TEST_ASSERT_EQUAL_STRING( "OtaErrUninitialized", str );
    err = OtaErrPanic;
    str = OTA_Err_strerror( err );
    TEST_ASSERT_EQUAL_STRING( "OtaErrPanic", str );
    err = OtaErrInvalidArg;
    str = OTA_Err_strerror( err );
    TEST_ASSERT_EQUAL_STRING( "OtaErrInvalidArg", str );
    err = OtaErrAgentStopped;
    str = OTA_Err_strerror( err );
    TEST_ASSERT_EQUAL_STRING( "OtaErrAgentStopped", str );
    err = OtaErrSignalEventFailed;
    str = OTA_Err_strerror( err );
    TEST_ASSERT_EQUAL_STRING( "OtaErrSignalEventFailed", str );
    err = OtaErrRequestJobFailed;
    str = OTA_Err_strerror( err );
    TEST_ASSERT_EQUAL_STRING( "OtaErrRequestJobFailed", str );
    err = OtaErrInitFileTransferFailed;
    str = OTA_Err_strerror( err );
    TEST_ASSERT_EQUAL_STRING( "OtaErrInitFileTransferFailed", str );
    err = OtaErrRequestFileBlockFailed;
    str = OTA_Err_strerror( err );
    TEST_ASSERT_EQUAL_STRING( "OtaErrRequestFileBlockFailed", str );
    err = OtaErrCleanupControlFailed;
    str = OTA_Err_strerror( err );
    TEST_ASSERT_EQUAL_STRING( "OtaErrCleanupControlFailed", str );
    err = OtaErrCleanupDataFailed;
    str = OTA_Err_strerror( err );
    TEST_ASSERT_EQUAL_STRING( "OtaErrCleanupDataFailed", str );
    err = OtaErrUpdateJobStatusFailed;
    str = OTA_Err_strerror( err );
    TEST_ASSERT_EQUAL_STRING( "OtaErrUpdateJobStatusFailed", str );
    err = OtaErrJobParserError;
    str = OTA_Err_strerror( err );
    TEST_ASSERT_EQUAL_STRING( "OtaErrJobParserError", str );
    err = OtaErrInvalidDataProtocol;
    str = OTA_Err_strerror( err );
    TEST_ASSERT_EQUAL_STRING( "OtaErrInvalidDataProtocol", str );
    err = OtaErrMomentumAbort;
    str = OTA_Err_strerror( err );
    TEST_ASSERT_EQUAL_STRING( "OtaErrMomentumAbort", str );
    err = OtaErrDowngradeNotAllowed;
    str = OTA_Err_strerror( err );
    TEST_ASSERT_EQUAL_STRING( "OtaErrDowngradeNotAllowed", str );
    err = OtaErrSameFirmwareVersion;
    str = OTA_Err_strerror( err );
    TEST_ASSERT_EQUAL_STRING( "OtaErrSameFirmwareVersion", str );
    err = OtaErrImageStateMismatch;
    str = OTA_Err_strerror( err );
    TEST_ASSERT_EQUAL_STRING( "OtaErrImageStateMismatch", str );
    err = OtaErrNoActiveJob;
    str = OTA_Err_strerror( err );
    TEST_ASSERT_EQUAL_STRING( "OtaErrNoActiveJob", str );
    err = OtaErrUserAbort;
    str = OTA_Err_strerror( err );
    TEST_ASSERT_EQUAL_STRING( "OtaErrUserAbort", str );
    err = OtaErrFailedToEncodeCbor;
    str = OTA_Err_strerror( err );
    TEST_ASSERT_EQUAL_STRING( "OtaErrFailedToEncodeCbor", str );
    err = OtaErrFailedToDecodeCbor;
    str = OTA_Err_strerror( err );
    TEST_ASSERT_EQUAL_STRING( "OtaErrFailedToDecodeCbor", str );
    err = OtaErrActivateFailed;
    str = OTA_Err_strerror( err );
    TEST_ASSERT_EQUAL_STRING( "OtaErrActivateFailed", str );
    err = OtaErrActivateFailed + 1;
    str = OTA_Err_strerror( err );
    TEST_ASSERT_EQUAL_STRING( "InvalidErrorCode", str );
}

/**
 * @brief Test OTA_OsStatus_strerror returns correct strings.
 */
void test_OTA_OsStatus_strerror( void )
{
    OtaOsStatus_t status;
    const char * str = NULL;

    status = OtaOsSuccess;
    str = OTA_OsStatus_strerror( status );
    TEST_ASSERT_EQUAL_STRING( "OtaOsSuccess", str );
    status = OtaOsEventQueueCreateFailed;
    str = OTA_OsStatus_strerror( status );
    TEST_ASSERT_EQUAL_STRING( "OtaOsEventQueueCreateFailed", str );
    status = OtaOsEventQueueSendFailed;
    str = OTA_OsStatus_strerror( status );
    TEST_ASSERT_EQUAL_STRING( "OtaOsEventQueueSendFailed", str );
    status = OtaOsEventQueueReceiveFailed;
    str = OTA_OsStatus_strerror( status );
    TEST_ASSERT_EQUAL_STRING( "OtaOsEventQueueReceiveFailed", str );
    status = OtaOsEventQueueDeleteFailed;
    str = OTA_OsStatus_strerror( status );
    TEST_ASSERT_EQUAL_STRING( "OtaOsEventQueueDeleteFailed", str );
    status = OtaOsTimerCreateFailed;
    str = OTA_OsStatus_strerror( status );
    TEST_ASSERT_EQUAL_STRING( "OtaOsTimerCreateFailed", str );
    status = OtaOsTimerStartFailed;
    str = OTA_OsStatus_strerror( status );
    TEST_ASSERT_EQUAL_STRING( "OtaOsTimerStartFailed", str );
    status = OtaOsTimerRestartFailed;
    str = OTA_OsStatus_strerror( status );
    TEST_ASSERT_EQUAL_STRING( "OtaOsTimerRestartFailed", str );
    status = OtaOsTimerStopFailed;
    str = OTA_OsStatus_strerror( status );
    TEST_ASSERT_EQUAL_STRING( "OtaOsTimerStopFailed", str );
    status = OtaOsTimerDeleteFailed;
    str = OTA_OsStatus_strerror( status );
    TEST_ASSERT_EQUAL_STRING( "OtaOsTimerDeleteFailed", str );
    status = OtaOsTimerDeleteFailed + 1;
    str = OTA_OsStatus_strerror( status );
    TEST_ASSERT_EQUAL_STRING( "InvalidErrorCode", str );
}

/**
 * @brief Test OTA_PalStatus_strerror returns correct strings.
 */
void test_OTA_PalStatus_strerror( void )
{
    OtaPalMainStatus_t status;
    const char * str = NULL;

    status = OtaPalSuccess;
    str = OTA_PalStatus_strerror( status );
    TEST_ASSERT_EQUAL_STRING( "OtaPalSuccess", str );
    status = OtaPalUninitialized;
    str = OTA_PalStatus_strerror( status );
    TEST_ASSERT_EQUAL_STRING( "OtaPalUninitialized", str );
    status = OtaPalOutOfMemory;
    str = OTA_PalStatus_strerror( status );
    TEST_ASSERT_EQUAL_STRING( "OtaPalOutOfMemory", str );
    status = OtaPalNullFileContext;
    str = OTA_PalStatus_strerror( status );
    TEST_ASSERT_EQUAL_STRING( "OtaPalNullFileContext", str );
    status = OtaPalSignatureCheckFailed;
    str = OTA_PalStatus_strerror( status );
    TEST_ASSERT_EQUAL_STRING( "OtaPalSignatureCheckFailed", str );
    status = OtaPalRxFileCreateFailed;
    str = OTA_PalStatus_strerror( status );
    TEST_ASSERT_EQUAL_STRING( "OtaPalRxFileCreateFailed", str );
    status = OtaPalRxFileTooLarge;
    str = OTA_PalStatus_strerror( status );
    TEST_ASSERT_EQUAL_STRING( "OtaPalRxFileTooLarge", str );
    status = OtaPalBootInfoCreateFailed;
    str = OTA_PalStatus_strerror( status );
    TEST_ASSERT_EQUAL_STRING( "OtaPalBootInfoCreateFailed", str );
    status = OtaPalBadSignerCert;
    str = OTA_PalStatus_strerror( status );
    TEST_ASSERT_EQUAL_STRING( "OtaPalBadSignerCert", str );
    status = OtaPalBadImageState;
    str = OTA_PalStatus_strerror( status );
    TEST_ASSERT_EQUAL_STRING( "OtaPalBadImageState", str );
    status = OtaPalAbortFailed;
    str = OTA_PalStatus_strerror( status );
    TEST_ASSERT_EQUAL_STRING( "OtaPalAbortFailed", str );
    status = OtaPalRejectFailed;
    str = OTA_PalStatus_strerror( status );
    TEST_ASSERT_EQUAL_STRING( "OtaPalRejectFailed", str );
    status = OtaPalCommitFailed;
    str = OTA_PalStatus_strerror( status );
    TEST_ASSERT_EQUAL_STRING( "OtaPalCommitFailed", str );
    status = OtaPalActivateFailed;
    str = OTA_PalStatus_strerror( status );
    TEST_ASSERT_EQUAL_STRING( "OtaPalActivateFailed", str );
    status = OtaPalFileAbort;
    str = OTA_PalStatus_strerror( status );
    TEST_ASSERT_EQUAL_STRING( "OtaPalFileAbort", str );
    status = OtaPalFileClose;
    str = OTA_PalStatus_strerror( status );
    TEST_ASSERT_EQUAL_STRING( "OtaPalFileClose", str );
    status = OtaPalFileClose + 1;
    str = OTA_PalStatus_strerror( status );
    TEST_ASSERT_EQUAL_STRING( "InvalidErrorCode", str );
}

/**
 * @brief Test OTA_JobParse_strerror returns correct strings.
 */
void test_OTA_JobParse_strerror( void )
{
    OtaJobParseErr_t status;
    const char * str = NULL;

    status = OtaJobParseErrUnknown;
    str = OTA_JobParse_strerror( status );
    TEST_ASSERT_EQUAL_STRING( "OtaJobParseErrUnknown", str );
    status = OtaJobParseErrNone;
    str = OTA_JobParse_strerror( status );
    TEST_ASSERT_EQUAL_STRING( "OtaJobParseErrNone", str );
    status = OtaJobParseErrNullJob;
    str = OTA_JobParse_strerror( status );
    TEST_ASSERT_EQUAL_STRING( "OtaJobParseErrNullJob", str );
    status = OtaJobParseErrUpdateCurrentJob;
    str = OTA_JobParse_strerror( status );
    TEST_ASSERT_EQUAL_STRING( "OtaJobParseErrUpdateCurrentJob", str );
    status = OtaJobParseErrZeroFileSize;
    str = OTA_JobParse_strerror( status );
    TEST_ASSERT_EQUAL_STRING( "OtaJobParseErrZeroFileSize", str );
    status = OtaJobParseErrNonConformingJobDoc;
    str = OTA_JobParse_strerror( status );
    TEST_ASSERT_EQUAL_STRING( "OtaJobParseErrNonConformingJobDoc", str );
    status = OtaJobParseErrBadModelInitParams;
    str = OTA_JobParse_strerror( status );
    TEST_ASSERT_EQUAL_STRING( "OtaJobParseErrBadModelInitParams", str );
    status = OtaJobParseErrNoContextAvailable;
    str = OTA_JobParse_strerror( status );
    TEST_ASSERT_EQUAL_STRING( "OtaJobParseErrNoContextAvailable", str );
    status = OtaJobParseErrNoActiveJobs;
    str = OTA_JobParse_strerror( status );
    TEST_ASSERT_EQUAL_STRING( "OtaJobParseErrNoActiveJobs", str );
    status = OtaJobParseErrNoActiveJobs + 1;
    str = OTA_JobParse_strerror( status );
    TEST_ASSERT_EQUAL_STRING( "InvalidErrorCode", str );
}

/**
 * @brief Test OTA_MQTT_strerror returns correct strings.
 */
void test_OTA_MQTT_strerror( void )
{
    OtaMqttStatus_t status;
    const char * str = NULL;

    status = OtaMqttSuccess;
    str = OTA_MQTT_strerror( status );
    TEST_ASSERT_EQUAL_STRING( "OtaMqttSuccess", str );
    status = OtaMqttPublishFailed;
    str = OTA_MQTT_strerror( status );
    TEST_ASSERT_EQUAL_STRING( "OtaMqttPublishFailed", str );
    status = OtaMqttSubscribeFailed;
    str = OTA_MQTT_strerror( status );
    TEST_ASSERT_EQUAL_STRING( "OtaMqttSubscribeFailed", str );
    status = OtaMqttUnsubscribeFailed;
    str = OTA_MQTT_strerror( status );
    TEST_ASSERT_EQUAL_STRING( "OtaMqttUnsubscribeFailed", str );
    status = OtaMqttUnsubscribeFailed + 1;
    str = OTA_MQTT_strerror( status );
    TEST_ASSERT_EQUAL_STRING( "InvalidErrorCode", str );
}

/**
 * @brief Test OTA_HTTP_strerror returns correct strings.
 */
void test_OTA_HTTP_strerror( void )
{
    OtaHttpStatus_t status;
    const char * str = NULL;

    status = OtaHttpSuccess;
    str = OTA_HTTP_strerror( status );
    TEST_ASSERT_EQUAL_STRING( "OtaHttpSuccess", str );
    status = OtaHttpInitFailed;
    str = OTA_HTTP_strerror( status );
    TEST_ASSERT_EQUAL_STRING( "OtaHttpInitFailed", str );
    status = OtaHttpDeinitFailed;
    str = OTA_HTTP_strerror( status );
    TEST_ASSERT_EQUAL_STRING( "OtaHttpDeinitFailed", str );
    status = OtaHttpRequestFailed;
    str = OTA_HTTP_strerror( status );
    TEST_ASSERT_EQUAL_STRING( "OtaHttpRequestFailed", str );
    status = OtaHttpRequestFailed + 1;
    str = OTA_HTTP_strerror( status );
    TEST_ASSERT_EQUAL_STRING( "InvalidErrorCode", str );
}

/* ========================================================================== */
/* ================== OTA State Machine Handler Unit Tests ================== */
/* ========================================================================== */

/**
 * @brief Test that initFileHandler returns the proper error when the timer
 *        fails to start.
 */
void test_OTA_initFileHandler_TimerFails( void )
{
    OtaEventMsg_t otaEvent = { 0 };

    /* Initialize the OTA interfaces so they are not NULL. */
    otaGoToState( OtaAgentStateReady );
    /* Fail to initialize the file transfer so the timer is started. */
    otaDataInterface.initFileTransfer = mockDataInterfaceInitFileTransferAlwaysFail;
    /* Fail to start the timer. */
    otaInterfaces.os.timer.start = mockOSTimerStartAlwaysFail;

    TEST_ASSERT_EQUAL( OtaErrInitFileTransferFailed, initFileHandler( otaEvent.pEventData ) );
}

/**
 * @brief Test that initFileHandler returns the proper error when the OTA event
 *        send functionality fails.
 */
void test_OTA_initFileHandler_EventSendFails( void )
{
    OtaEventMsg_t otaEvent = { 0 };

    /* Initialize the OTA interfaces so they are not NULL. */
    otaGoToState( OtaAgentStateReady );

    /* Test failing while trying to send the shutdown event after failing
     * to initialize the file. */
    /* Fail to initialize the file transfer so the timer is started. */
    otaDataInterface.initFileTransfer = mockDataInterfaceInitFileTransferAlwaysFail;

    /* Simulate reaching the maximum number of attempts before considering
     * the attempt to be a failure. */
    otaAgent.requestMomentum = otaconfigMAX_NUM_REQUEST_MOMENTUM;
    /* Fail to send the OTA event. */
    otaInterfaces.os.event.send = mockOSEventSendAlwaysFail;

    TEST_ASSERT_EQUAL( OtaErrSignalEventFailed, initFileHandler( otaEvent.pEventData ) );

    /* Test failing while trying to send the request block event after
     * successfully initializing the file. */

    /* Succeed with the file initialization to then attempt to send the event
     * for requesting a block. */
    otaDataInterface.initFileTransfer = mockDataInitFileTransferAlwaysSucceed;
    /* Fail to send the OTA event. */
    otaInterfaces.os.event.send = mockOSEventSendAlwaysFail;

    TEST_ASSERT_EQUAL( OtaErrSignalEventFailed, initFileHandler( otaEvent.pEventData ) );
}

/**
 * @brief Test that requestDataHandler returns the proper error when the OTA
 *        event send functionality fails.
 */
void test_OTA_requestDataHandler_EventSendFails( void )
{
    OtaEventMsg_t otaEvent = { 0 };

    /* Initialize the OTA interfaces so they are not NULL. */
    otaGoToState( OtaAgentStateReady );

    /* File context has a non-zero number of blocks remaining. */
    otaAgent.fileContext.blocksRemaining = 1U;

    /* Simulate reaching the maximum number of attempts before considering
     * the attempt to be a failure. In this scenario, the handler will attempt
     * to send a shutdown event to the OTA Agent.*/
    otaAgent.requestMomentum = otaconfigMAX_NUM_REQUEST_MOMENTUM;
    /* Fail to send the OTA event. */
    otaInterfaces.os.event.send = mockOSEventSendAlwaysFail;

    TEST_ASSERT_EQUAL( OtaErrSignalEventFailed, requestDataHandler( otaEvent.pEventData ) );
}

/**
 * @brief Test that requestJobHandler returns the proper error when the timer
 *        start functionality fails.
 */
void test_OTA_requestJobHandler_TimerFails( void )
{
    OtaEventMsg_t otaEvent = { 0 };

    /* Initialize the OTA interfaces so they are not NULL. */
    otaGoToState( OtaAgentStateReady );

    /* Fail requesting the job document. */
    otaControlInterface.requestJob = mockControlInterfaceRequestJobAlwaysFail;
    /* Fail to start the request timer. */
    otaInterfaces.os.timer.start = mockOSTimerStartAlwaysFail;

    TEST_ASSERT_EQUAL( OtaErrRequestJobFailed, requestJobHandler( otaEvent.pEventData ) );
}

/**
 * @brief Test that requestJobHandler returns the proper error when the OTA
 *        event send functionality fails.
 */
void test_OTA_requestJobHandler_EventSendFails( void )
{
    OtaEventMsg_t otaEvent = { 0 };

    /* Initialize the OTA interfaces so they are not NULL. */
    otaGoToState( OtaAgentStateReady );

    /* Fail requesting the job document. */
    otaControlInterface.requestJob = mockControlInterfaceRequestJobAlwaysFail;

    /* Simulate reaching the maximum number of attempts before considering
     * the attempt to be a failure. */
    otaAgent.requestMomentum = otaconfigMAX_NUM_REQUEST_MOMENTUM;
    /* Fail to send the OTA event. */
    otaInterfaces.os.event.send = mockOSEventSendAlwaysFail;

    TEST_ASSERT_EQUAL( OtaErrSignalEventFailed, requestJobHandler( otaEvent.pEventData ) );
}

/**
 * @brief Test that processDataHandler safely handles receiving invalid events.
 */
void test_OTA_processDataHandler_InvalidEvent( void )
{
    /* Initialize the OTA interfaces so they are not NULL. */
    otaGoToState( OtaAgentStateReady );

    /* Test that passing NULL event data does not cause a segmentation fault.
     * The expected return is OtaErrNone because the error return value of this
     * handler represents the success of updating the job document when there
     * is an issue processing the block. */
    TEST_ASSERT_EQUAL( OtaErrNone, processDataHandler( NULL ) );
}

/**
 * @brief Test that resumeHandler returns the proper error when the OTA event
 *        send functionality fails.
 */
void test_OTA_resumeHandler_EventSendFails()
{
    /* Initialize the OTA interfaces so they are not NULL. */
    otaGoToState( OtaAgentStateSuspended );

    /* Fail to send the OTA event. */
    otaInterfaces.os.event.send = mockOSEventSendAlwaysFail;

    TEST_ASSERT_EQUAL( OtaErrSignalEventFailed, resumeHandler( NULL ) );
}

void test_OTA_jobNotificationHandler_EventSendFails()
{
    /* Initialize the OTA interfaces so they are not NULL. */
    otaGoToState( OtaAgentStateWaitingForFileBlock );

    otaInterfaces.os.event.send = mockOSEventSendAlwaysFail;

    TEST_ASSERT_EQUAL( OtaErrSignalEventFailed, jobNotificationHandler( NULL ) );
}

/**
 * @brief Test that shutdownHandler safely handles being called without the
 *        control and data interfaces being set.
 */
void test_OTA_shutdownHandler_NullInterface()
{
    otaGoToState( OtaAgentStateReady );

    otaDataInterface.cleanup = NULL;
    otaDataInterface.decodeFileBlock = NULL;
    otaDataInterface.initFileTransfer = NULL;
    otaDataInterface.requestFileBlock = NULL;

    otaControlInterface.cleanup = NULL;
    otaControlInterface.requestJob = NULL;
    otaControlInterface.updateJobStatus = NULL;

    TEST_ASSERT_EQUAL( OtaErrNone, shutdownHandler( NULL ) );

    /* Set state to stopped manually. */
    otaAgent.state = OtaAgentStateStopped;
}

/* No OTA interface available when processing events. */
void test_OTA_nullOtaInterfaceWhenProcessEvent()
{
    otaInitDefault();
    otaGoToState( OtaAgentStateReady );
    TEST_ASSERT_EQUAL( OtaAgentStateReady, OTA_GetState() );

    /* Set OTA interface to NULL. */
    otaAgent.pOtaInterface = NULL;

    receiveAndProcessOtaEvent();

    TEST_ASSERT_EQUAL( OtaAgentStateReady, OTA_GetState() );

    /* Reset OTA interface. */
    otaAgent.pOtaInterface = &otaInterfaces;
}

/* Send event to OTA library when it's stopped. */
void test_OTA_sendEventWhenStopped()
{
    OtaEventMsg_t eventMsg = { 0 };

    tearDown();
    TEST_ASSERT_EQUAL( OtaAgentStateStopped, OTA_GetState() );

    eventMsg.eventId = OtaAgentEventStart;

    TEST_ASSERT_EQUAL( false, OTA_SignalEvent( &eventMsg ) );
}

/* Re-start OTA library after shutdown. */
void test_OTA_restartOtaAfterShutdown()
{
    /* First initialize OTA library. */
    otaInitDefault();
    otaGoToState( OtaAgentStateReady );
    TEST_ASSERT_EQUAL( OtaAgentStateReady, OTA_GetState() );

    /* Shut down OTA. */
    tearDown();
    TEST_ASSERT_EQUAL( OtaAgentStateStopped, OTA_GetState() );

    /* Second initialize OTA library. */
    setUp();
    otaInitDefault();
    otaGoToState( OtaAgentStateReady );
    TEST_ASSERT_EQUAL( OtaAgentStateReady, OTA_GetState() );
}

/* Re-start OTA library and then drop events after shutdown. */
void test_OTA_restartOtaAfterShutdownAndDropEvents()
{
    /* First initialize OTA library */
    otaInitDefault();
    otaGoToState( OtaAgentStateReady );
    TEST_ASSERT_EQUAL( OtaAgentStateReady, OTA_GetState() );

    /* Shut down OTA. */
    tearDown();
    TEST_ASSERT_EQUAL( OtaAgentStateStopped, OTA_GetState() );

    /* Put some fake events to test if OTA drops them correctly. */
    otaEventQueueEnd->eventId = OtaAgentEventSuspend;
    otaEventQueueEnd->pEventData = NULL;
    otaEventQueueEnd++;
    otaEventQueueEnd->eventId = OtaAgentEventUserAbort;
    otaEventQueueEnd->pEventData = NULL;
    otaEventQueueEnd++;

    /* Second initialize OTA library */
    setUp();
    otaInitDefault();
    otaGoToState( OtaAgentStateReady );
    TEST_ASSERT_EQUAL( OtaAgentStateReady, OTA_GetState() );
}

/* ========================================================================== */
/* ======================== OTA Interface Unit Tests ======================== */
/* ========================================================================== */

/**
 * @brief Test that setDataInterface sets the data interface when given valid
 *        inputs.
 */
void test_OTA_setDataInterface_ValidInput( void )
{
    OtaDataInterface_t dataInterface = { NULL, NULL, NULL, NULL };
    uint8_t pProtocol[ OTA_PROTOCOL_BUFFER_SIZE ] = { 0 };

    memcpy( pProtocol, "[\"MQTT\"]", sizeof( "[\"MQTT\"]" ) );
    TEST_ASSERT_EQUAL( OtaErrNone, setDataInterface( &dataInterface, pProtocol ) );
    TEST_ASSERT_EQUAL( initFileTransfer_Mqtt, dataInterface.initFileTransfer );
    TEST_ASSERT_EQUAL( requestFileBlock_Mqtt, dataInterface.requestFileBlock );
    TEST_ASSERT_EQUAL( decodeFileBlock_Mqtt, dataInterface.decodeFileBlock );
    TEST_ASSERT_EQUAL( cleanupData_Mqtt, dataInterface.cleanup );

    memcpy( pProtocol, "[\"HTTP\"]", sizeof( "[\"HTTP\"]" ) );
    memset( &dataInterface, 0, sizeof( dataInterface ) );
    TEST_ASSERT_EQUAL( OtaErrNone, setDataInterface( &dataInterface, pProtocol ) );
    TEST_ASSERT_EQUAL( initFileTransfer_Http, dataInterface.initFileTransfer );
    TEST_ASSERT_EQUAL( requestDataBlock_Http, dataInterface.requestFileBlock );
    TEST_ASSERT_EQUAL( decodeFileBlock_Http, dataInterface.decodeFileBlock );
    TEST_ASSERT_EQUAL( cleanupData_Http, dataInterface.cleanup );

    memcpy( pProtocol, "[\"MQTT\",\"HTTP\"]", sizeof( "[\"MQTT\",\"HTTP\"]" ) );
    memset( &dataInterface, 0, sizeof( dataInterface ) );
    TEST_ASSERT_EQUAL( OtaErrNone, setDataInterface( &dataInterface, pProtocol ) );
    TEST_ASSERT_NOT_EQUAL( NULL, dataInterface.initFileTransfer );
    TEST_ASSERT_NOT_EQUAL( NULL, dataInterface.requestFileBlock );
    TEST_ASSERT_NOT_EQUAL( NULL, dataInterface.decodeFileBlock );
    TEST_ASSERT_NOT_EQUAL( NULL, dataInterface.cleanup );

    memcpy( pProtocol, "[\"HTTP\",\"MQTT\"]", sizeof( "[\"HTTP\",\"MQTT\"]" ) );
    memset( &dataInterface, 0, sizeof( dataInterface ) );
    TEST_ASSERT_EQUAL( OtaErrNone, setDataInterface( &dataInterface, pProtocol ) );
    TEST_ASSERT_NOT_EQUAL( NULL, dataInterface.initFileTransfer );
    TEST_ASSERT_NOT_EQUAL( NULL, dataInterface.requestFileBlock );
    TEST_ASSERT_NOT_EQUAL( NULL, dataInterface.decodeFileBlock );
    TEST_ASSERT_NOT_EQUAL( NULL, dataInterface.cleanup );
}

/**
 * @brief Test that setDataInterface returns an error and does not set the data
 * interface when provided with an invalid input from a job document.
 */
void test_OTA_setDataInterface_InvalidInput( void )
{
    OtaDataInterface_t dataInterface = { NULL, NULL, NULL, NULL };
    uint8_t pProtocol[ OTA_PROTOCOL_BUFFER_SIZE ] = { 0 };

    memcpy( pProtocol, "invalid_protocol", sizeof( "invalid_protocol" ) );
    TEST_ASSERT_EQUAL( OtaErrInvalidDataProtocol, setDataInterface( &dataInterface, pProtocol ) );
    TEST_ASSERT_EQUAL( NULL, dataInterface.initFileTransfer );
    TEST_ASSERT_EQUAL( NULL, dataInterface.requestFileBlock );
    TEST_ASSERT_EQUAL( NULL, dataInterface.decodeFileBlock );
    TEST_ASSERT_EQUAL( NULL, dataInterface.cleanup );

    memcpy( pProtocol, "junkMQTT", sizeof( "junkMQTT" ) );
    TEST_ASSERT_EQUAL( OtaErrInvalidDataProtocol, setDataInterface( &dataInterface, pProtocol ) );
    TEST_ASSERT_EQUAL( NULL, dataInterface.initFileTransfer );
    TEST_ASSERT_EQUAL( NULL, dataInterface.requestFileBlock );
    TEST_ASSERT_EQUAL( NULL, dataInterface.decodeFileBlock );
    TEST_ASSERT_EQUAL( NULL, dataInterface.cleanup );

    memcpy( pProtocol, "HTTPjunk", sizeof( "HTTPjunk" ) );
    TEST_ASSERT_EQUAL( OtaErrInvalidDataProtocol, setDataInterface( &dataInterface, pProtocol ) );
    TEST_ASSERT_EQUAL( NULL, dataInterface.initFileTransfer );
    TEST_ASSERT_EQUAL( NULL, dataInterface.requestFileBlock );
    TEST_ASSERT_EQUAL( NULL, dataInterface.decodeFileBlock );
    TEST_ASSERT_EQUAL( NULL, dataInterface.cleanup );
}


/* ========================================================================== */
/* ==================== OTA Private Function Unit Tests ===================== */
/* ========================================================================== */

void test_OTA_initDocModelFail()
{
    DocParseErr_t parseError = DocParseErrNone;
    JsonDocModel_t otaJobDocModel;

    parseError = initDocModel( NULL,
                               otaJobDocModelParamStructure,
                               ( void * ) &( otaAgent.fileContext ),
                               ( uint32_t ) sizeof( OtaFileContext_t ),
                               OTA_NUM_JOB_PARAMS );
    TEST_ASSERT_EQUAL( DocParseErrNullModelPointer, parseError );

    parseError = initDocModel( &otaJobDocModel,
                               NULL,
                               ( void * ) &( otaAgent.fileContext ),
                               ( uint32_t ) sizeof( OtaFileContext_t ),
                               OTA_NUM_JOB_PARAMS );
    TEST_ASSERT_EQUAL( DocParseErrNullBodyPointer, parseError );

    parseError = initDocModel( &otaJobDocModel,
                               otaJobDocModelParamStructure,
                               ( void * ) &( otaAgent.fileContext ),
                               ( uint32_t ) sizeof( OtaFileContext_t ),
                               OTA_DOC_MODEL_MAX_PARAMS + 1 );
    TEST_ASSERT_EQUAL( DocParseErrTooManyParams, parseError );
}

void test_OTA_parseJobFailsNullJsonDocument()
{
    OtaFileContext_t * pContext = NULL;
    bool updateJob = false;

    otaInitDefault();
    pContext = parseJobDoc( NULL, 0, JOB_DOC_A, strlen( JOB_DOC_A ), &updateJob );

    TEST_ASSERT_NULL( pContext );
    TEST_ASSERT_EQUAL( false, updateJob );
}

void test_OTA_extractParameterFailInvalidJobDocModel()
{
    OtaFileContext_t * pContext;
    bool updateJob = false;
    JsonDocParam_t otaCustomJobDocModelParamStructure[ 1 ] =
    {
        { OTA_JSON_JOB_ID_KEY, OTA_JOB_PARAM_REQUIRED, U16_OFFSET( OtaFileContext_t, pJobName ), U16_OFFSET( OtaFileContext_t, jobNameMaxSize ), UINT16_MAX },
    };

    /* The document structure has an invalid value for ModelParamType_t. */

    otaInitDefault();
    pContext = parseJobDoc( otaCustomJobDocModelParamStructure, 1, JOB_DOC_A, strlen( JOB_DOC_A ), &updateJob );

    TEST_ASSERT_NULL( pContext );
    TEST_ASSERT_EQUAL( false, updateJob );
}

void test_OTA_validateJSONFailNullJson()
{
    DocParseErr_t err = DocParseErrNone;

    err = validateJSON( NULL, 0 );
    TEST_ASSERT_EQUAL( DocParseErrNullDocPointer, err );
}

void test_OTA_validateDataBlockInputSize()
{
    OtaFileContext_t fileContext = { 0 };

    /* Test for when the block received is the final block. */
    fileContext.fileSize = OTA_FILE_BLOCK_SIZE;
    /* Block size is too small. */
    TEST_ASSERT_EQUAL( false, validateDataBlock( &fileContext, 0, 0 ) );
    /* Block size is the expected size. */
    TEST_ASSERT_EQUAL( true, validateDataBlock( &fileContext, 0, OTA_FILE_BLOCK_SIZE ) );
    /* Block size is larger than the expected size. */
    TEST_ASSERT_EQUAL( false, validateDataBlock( &fileContext, 0, OTA_FILE_BLOCK_SIZE + 1 ) );

    /* Test for when the block is not the final block. */
    fileContext.fileSize = OTA_FILE_BLOCK_SIZE * 2;
    /* Block size is too small. */
    TEST_ASSERT_EQUAL( false, validateDataBlock( &fileContext, 0, 0 ) );
    /* Block size is the expected size. */
    TEST_ASSERT_EQUAL( true, validateDataBlock( &fileContext, 0, OTA_FILE_BLOCK_SIZE ) );
    /* Block size is larger than the expected size. */
    TEST_ASSERT_EQUAL( false, validateDataBlock( &fileContext, 0, OTA_FILE_BLOCK_SIZE + 1 ) );
}

void test_ingestDataBlockCleanup_NullFile()
{
    OtaFileContext_t fileContext = { 0 };
    OtaPalStatus_t closeStatus = { 0 };

    otaGoToState( OtaAgentStateReady );

    fileContext.pRxBlockBitmap = NULL;
    fileContext.blocksRemaining = 0;
    fileContext.pFile = NULL;

    TEST_ASSERT_EQUAL( IngestResultBadFileHandle, ingestDataBlockCleanup( &fileContext, &closeStatus ) );
}

void test_verifyActiveJobStatus_NullJobName()
{
    OtaFileContext_t fileContext = { 0 };
    OtaFileContext_t finalFile = { 0 };
    OtaFileContext_t * pFinalFile = &finalFile;
    bool shouldUpdate = false;

    TEST_ASSERT_EQUAL( OtaJobParseErrNullJob, verifyActiveJobStatus( &fileContext, &pFinalFile, &shouldUpdate ) );
}

void test_verifyActiveJobStatus_NullUpdateURL()
{
    OtaFileContext_t fileContext = { 0 };
    OtaFileContext_t finalFile = { 0 };
    OtaFileContext_t * pFinalFile = &finalFile;
    bool shouldUpdate = false;

    /* Set the job names to be the same to simulate receiving a job doc with the same ID. */
    ( void ) memcpy( otaAgent.pActiveJobName, "jobName", sizeof( "jobName" ) );
    fileContext.pJobName = ( uint8_t * ) "jobName";
    /* Set the pUpdateUrlPath to NULL. */
    otaAgent.fileContext.pUpdateUrlPath = NULL;

    TEST_ASSERT_EQUAL( OtaJobParseErrUpdateCurrentJob, verifyActiveJobStatus( &fileContext, &pFinalFile, &shouldUpdate ) );
}

void test_verifyActiveJobStatus_NullCleanupInterface()
{
    OtaFileContext_t fileContext = { 0 };
    OtaFileContext_t finalFile = { 0 };
    OtaFileContext_t * pFinalFile = &finalFile;
    bool shouldUpdate = false;

    otaGoToState( OtaAgentStateReady );

    /* Make it so that the job document names do not match. This simulates
     * receiving a new job document. In this scenario, the OTA Agent will drop
     * the old job. */
    fileContext.pJobName = ( uint8_t * ) "jobName";
    memset( otaAgent.pActiveJobName, 0, OTA_JOB_ID_MAX_SIZE );

    /* Set the data interface for cleanup to NULL. */
    otaDataInterface.cleanup = NULL;

    /* The verifyActiveJobStatus function is expected to safely avoid calling
     * the cleanup function if it is not defined. */
    TEST_ASSERT_EQUAL( OtaJobParseErrNone, verifyActiveJobStatus( &fileContext, &pFinalFile, &shouldUpdate ) );
}

/* This test is to check if the library handles the situation where the size of the
 * file downloaded using OTA is greater than the maximum size supported by the library. */
void test_OTA_overflowFileSize()
{
    pOtaJobDoc = JOB_DOC_FILESIZE_OVERFLOW;

    otaGoToState( OtaAgentStateWaitingForJob );
    TEST_ASSERT_EQUAL( OtaAgentStateWaitingForJob, OTA_GetState() );

    otaReceiveJobDocument();
    receiveAndProcessOtaEvent();

    TEST_ASSERT_EQUAL( OtaAgentStateWaitingForJob, OTA_GetState() );
}

/* This test is to check if the number of ota packets received by the device does not
 * exceed the maximum limit of its datatype. */
void test_OTA_packetsProcessedOverflow()
{
    OtaEventMsg_t otaEvent;
    OtaEventData_t eventBuffers[ OTA_TEST_FILE_NUM_BLOCKS * OTA_TEST_DUPLICATE_NUM_BLOCKS ];
    uint8_t pFileBlock[ OTA_FILE_BLOCK_SIZE ] = { 0 };
    uint8_t pStreamingMessage[ OTA_FILE_BLOCK_SIZE * 2 ] = { 0 };
    size_t streamingMessageSize = 0;
    int remainingBytes = OTA_TEST_FILE_SIZE;
    int idx = 0;
    int dupIdx = 0;

    otaGoToState( OtaAgentStateWaitingForFileBlock );
    TEST_ASSERT_EQUAL( OtaAgentStateWaitingForFileBlock, OTA_GetState() );

    /* Set the event send interface to a mock function that allows events to be sent continuously
     * because we're receiving multiple blocks in this test. */
    otaInterfaces.os.event.send = mockOSEventSend;

    /* Fill the file block. */
    for( idx = 0; idx < ( int ) sizeof( pFileBlock ); idx++ )
    {
        pFileBlock[ idx ] = idx % UINT8_MAX;
    }

    /* Send blocks. */
    idx = 0;

    while( remainingBytes >= 0 )
    {
        /* Intentionally send duplicate blocks to test if we are handling it correctly. */
        for( dupIdx = 0; dupIdx < OTA_TEST_DUPLICATE_NUM_BLOCKS; dupIdx++ )
        {
            /* Construct a AWS IoT streaming message. */
            createOtaStreamingMessage(
                pStreamingMessage,
                sizeof( pStreamingMessage ),
                idx,
                pFileBlock,
                min( ( uint32_t ) remainingBytes, OTA_FILE_BLOCK_SIZE ),
                &streamingMessageSize,
                true );

            otaEvent.eventId = OtaAgentEventReceivedFileBlock;
            otaEvent.pEventData = &eventBuffers[ idx * OTA_TEST_DUPLICATE_NUM_BLOCKS + dupIdx ];
            memcpy( otaEvent.pEventData->data, pStreamingMessage, streamingMessageSize );
            otaEvent.pEventData->dataLength = streamingMessageSize;
            OTA_SignalEvent( &otaEvent );
        }

        idx++;
        remainingBytes -= OTA_FILE_BLOCK_SIZE;
    }

    /* Process all of the events for receiving an MQTT message. */
    TEST_ASSERT_EQUAL( 0, otaAgent.statistics.otaPacketsProcessed );

    otaAgent.statistics.otaPacketsProcessed = UINT32_MAX;

    processEntireQueue();

    /* OTA agent should complete the update and go back to waiting for job state. */
    receiveAndProcessOtaEvent();

    /* Check if received complete file. */
    for( idx = 0; idx < OTA_TEST_FILE_SIZE; ++idx )
    {
        TEST_ASSERT_EQUAL( pFileBlock[ idx % sizeof( pFileBlock ) ], pOtaFileBuffer[ idx ] );
    }
}

/* This test is to check if the library handles the situation where the length of the
 * job name downloaded using OTA is greater than the maximum size supported by the library. */
void test_OTA_jobIdMaxLength()
{
    pOtaJobDoc = JOB_DOC_INVALID_JOB_ID_LEN_MAX;

    otaGoToState( OtaAgentStateWaitingForJob );
    TEST_ASSERT_EQUAL( OtaAgentStateWaitingForJob, OTA_GetState() );

    otaReceiveJobDocument();
    receiveAndProcessOtaEvent();

    TEST_ASSERT_EQUAL( OtaAgentStateWaitingForJob, OTA_GetState() );
}

/* Enlarge job name and size in doc param to simulate if the size of pJobNameBuffer in ota.c
 * and pActiveJobName in OtaAgentContext_t is different. */
void test_OTA_jobBufferLargerThanpActiveJobName()
{
    pOtaJobDoc = JOB_DOC_INVALID_JOB_ID_LEN_MAX;

    otaGoToState( OtaAgentStateWaitingForJob );
    TEST_ASSERT_EQUAL( OtaAgentStateWaitingForJob, OTA_GetState() );

    /* Initialize JOB Id buffer .*/
    otaAgent.fileContext.pJobName = pLargerJobNameBuffer;
    otaAgent.fileContext.jobNameMaxSize = ( uint16_t ) sizeof( pLargerJobNameBuffer );

    otaReceiveJobDocument();
    receiveAndProcessOtaEvent();

    TEST_ASSERT_EQUAL( OtaAgentStateWaitingForJob, OTA_GetState() );
}
