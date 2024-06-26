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
 * @file ota_private.h
 * @brief Macros, enums, variables, and definitions internal to the OTA Agent module and
 * shared by other OTA modules and testing files.
 */

#ifndef OTA_PRIVATE_H
#define OTA_PRIVATE_H

/* *INDENT-OFF* */
#ifdef __cplusplus
    extern "C" {
#endif
/* *INDENT-ON* */

/* Standard includes. */
/* For FILE type in OtaFileContext_t.*/
#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>

/* OTA_DO_NOT_USE_CUSTOM_CONFIG allows building the OTA library
 * without a custom config. If a custom config is provided, the
 * OTA_DO_NOT_USE_CUSTOM_CONFIG macro should not be defined. */
#ifndef OTA_DO_NOT_USE_CUSTOM_CONFIG
    #include "ota_config.h"
#endif

/* Include config defaults header to get default values of configs not defined
 * in ota_config.h file. */
#include "ota_config_defaults.h"

/**
 * @addtogroup ota_constants
 * @{
 */
/* General constants. */
#define LOG2_BITS_PER_BYTE           3U                                                   /*!< @brief Log base 2 of bits per byte. */
#define BITS_PER_BYTE                ( ( uint32_t ) 1U << LOG2_BITS_PER_BYTE )            /*!< @brief Number of bits in a byte. This is used by the block bitmap implementation. */
#define OTA_FILE_BLOCK_SIZE          ( ( uint32_t ) 1U << otaconfigLOG2_FILE_BLOCK_SIZE ) /*!< @brief Data section size of the file data block message (excludes the header). */
#define OTA_MAX_FILES                1U                                                   /*!< @brief [MUST REMAIN 1! Future support.] Maximum number of concurrent OTA files. */
#define OTA_MAX_BLOCK_BITMAP_SIZE    128U                                                 /*!< @brief Max allowed number of bytes to track all blocks of an OTA file. Adjust block size if more range is needed. */
#define OTA_REQUEST_MSG_MAX_SIZE     ( 3U * OTA_MAX_BLOCK_BITMAP_SIZE )                   /*!< @brief Maximum size of the message */
#define OTA_REQUEST_URL_MAX_SIZE     ( 1500 )                                             /*!< @brief Maximum size of the S3 presigned URL */
#define OTA_ERASED_BLOCKS_VAL        0xffU                                                /*!< @brief The starting state of a group of erased blocks in the Rx block bitmap. */
#define OTA_MAX_FILE_SIZE            UINT32_MAX - OTA_FILE_BLOCK_SIZE + 1U                /*!< @brief The maximum file size supported by the library. */
/** @} */

/**
 * @addtogroup ota_constants
 * @{
 */
/* Job document parser constants. */
#define OTA_MAX_JSON_TOKENS         64U                                                                         /*!< @brief Number of JSON tokens supported in a single parser call. */
#define OTA_MAX_JSON_STR_LEN        256U                                                                        /*!< @brief Limit our JSON string compares to something small to avoid going into the weeds. */
#define OTA_DOC_MODEL_MAX_PARAMS    32U                                                                         /*!< @brief The parameter list is backed by a 32 bit longword bitmap by design. */
#define OTA_JOB_PARAM_REQUIRED      ( bool ) true                                                               /*!< @brief Used to denote a required document model parameter. */
#define OTA_JOB_PARAM_OPTIONAL      ( bool ) false                                                              /*!< @brief Used to denote an optional document model parameter. */
#define OTA_DONT_STORE_PARAM        0xffff                                                                      /*!< @brief If destOffset in the model is 0xffffffff, do not store the value. */
#define OTA_STORE_NESTED_JSON       0x1fffU                                                                     /*!< @brief Store the reference to a nested JSON in a separate pointer */
#define OTA_DATA_BLOCK_SIZE         ( ( 1U << otaconfigLOG2_FILE_BLOCK_SIZE ) + OTA_REQUEST_URL_MAX_SIZE + 30 ) /*!< @brief Header is 19 bytes.*/
/** @} */

/**
 * @addtogroup ota_constants
 * @{
 */
/* OTA Agent task event flags. */
#define OTA_EVT_MASK_JOB_MSG_READY     0x00000001UL                                                                                                                               /*!< Event flag for OTA Job message ready. */
#define OTA_EVT_MASK_DATA_MSG_READY    0x00000002UL                                                                                                                               /*!< Event flag for OTA Data message ready. */
#define OTA_EVT_MASK_SHUTDOWN          0x00000004UL                                                                                                                               /*!< Event flag to request OTA shutdown. */
#define OTA_EVT_MASK_REQ_TIMEOUT       0x00000008UL                                                                                                                               /*!< Event flag indicating the request timer has timed out. */
#define OTA_EVT_MASK_USER_ABORT        0x000000016UL                                                                                                                              /*!< Event flag to indicate user initiated OTA abort. */
#define OTA_EVT_MASK_ALL_EVENTS        ( OTA_EVT_MASK_JOB_MSG_READY | OTA_EVT_MASK_DATA_MSG_READY | OTA_EVT_MASK_SHUTDOWN | OTA_EVT_MASK_REQ_TIMEOUT | OTA_EVT_MASK_USER_ABORT )  /*!< Event flag to mask indicate all events.*/
/** @} */

/**
 * @brief Number of parameters in the job document.
 *
 */
#define OTA_NUM_JOB_PARAMS          ( 21 )

/**
 * @brief Maximum size of the Job ID.
 *
 */
#define OTA_JOB_ID_MAX_SIZE         ( 72UL + 1UL )

/**
 * @brief Size of the buffer used to store the protocol field of the job document.
 *
 */
#define OTA_PROTOCOL_BUFFER_SIZE    20U

/**
 * @ingroup ota_constants
 * @brief A composite cryptographic signature structure able to hold our largest supported signature.
 */

#define kOTA_MaxSignatureSize           384 /* Max bytes supported for a file signature (3072 bit RSA is 384 bytes). */

/**
 *
 * @brief Keys in OTA job doc.
 *
 * The OTA job document contains parameters that are required for us to build the
 * stream request message and manage the OTA process. Including info like file name,
 * size, attributes, etc. The following value specifies the number of parameters
 * that are included in the job document model although some may be optional.
 * @addtogroup ota_constants
 * @{
 */
#define OTA_JSON_SEPARATOR              "."                                                        /*!< @brief Separator used to define nested keys. */
#define OTA_JSON_CLIENT_TOKEN_KEY       "clientToken"                                              /*!< @brief Client token. */
#define OTA_JSON_TIMESTAMP_KEY          "timestamp"                                                /*!< @brief Used to calculate timeout and time spent on the operation. */
#define OTA_JSON_EXECUTION_KEY          "execution"                                                /*!< @brief Contains job execution parameters . */
#define OTA_JSON_JOB_ID_KEY             OTA_JSON_EXECUTION_KEY OTA_JSON_SEPARATOR "jobId"          /*!< @brief Name of the job. */
#define OTA_JSON_STATUS_DETAILS_KEY     OTA_JSON_EXECUTION_KEY OTA_JSON_SEPARATOR "statusDetails"  /*!< @brief Current status of the job. */
#define OTA_JSON_SELF_TEST_KEY          OTA_JSON_STATUS_DETAILS_KEY OTA_JSON_SEPARATOR "self_test" /*!< @brief Specifies if the platform and service is is selftest. */
#define OTA_JSON_UPDATED_BY_KEY         OTA_JSON_STATUS_DETAILS_KEY OTA_JSON_SEPARATOR "updatedBy" /*!< @brief Parameter to specify update status. */
#define OTA_JSON_UPDATED_BY_KEY_ONLY    "updatedBy"                                                /*!< @brief Specifies if the platform and service is is selftest. Not searched in sub fields. */
#define OTA_JSON_SELF_TEST_KEY_ONLY     "self_test"                                                /*!< @brief Parameter to specify update status. Not searched in sub fields. */
#define OTA_JSON_JOB_DOC_KEY            OTA_JSON_EXECUTION_KEY OTA_JSON_SEPARATOR "jobDocument"    /*!< @brief Parameters that specify the nature of the job. */
#define OTA_JSON_OTA_UNIT_KEY           OTA_JSON_JOB_DOC_KEY OTA_JSON_SEPARATOR "afr_ota"          /*!< @brief afr-ota. */
#define OTA_JSON_PROTOCOLS_KEY          OTA_JSON_OTA_UNIT_KEY OTA_JSON_SEPARATOR "protocols"       /*!< @brief Protocols over which the download can take place. */
#define OTA_JSON_FILE_GROUP_KEY         OTA_JSON_OTA_UNIT_KEY OTA_JSON_SEPARATOR "files"           /*!< @brief Parameters for specifying file configurations. */
#define OTA_JSON_STREAM_NAME_KEY        OTA_JSON_OTA_UNIT_KEY OTA_JSON_SEPARATOR "streamname"      /*!< @brief Name of the stream used for download. */
#define OTA_JSON_FILE_PATH_KEY          "filepath"                                                 /*!< @brief Path to store the image on the device. */
#define OTA_JSON_FILE_SIZE_KEY          "filesize"                                                 /*!< @brief Size of the file to be downloaded. */
#define OTA_JSON_FILE_ID_KEY            "fileid"                                                   /*!< @brief Used to identify the file in case of multiple file downloads. */
#define OTA_JSON_FILE_ATTRIBUTE_KEY     "attr"                                                     /*!< @brief Additional file attributes. */
#define OTA_JSON_FILE_CERT_NAME_KEY     "certfile"                                                 /*!< @brief Location of the certificate on the device to find code signing. */
#define OTA_JSON_UPDATE_DATA_URL_KEY    "update_data_url"                                          /*!< @brief S3 bucket presigned url to fetch the image from . */
#define OTA_JSON_AUTH_SCHEME_KEY        "auth_scheme"                                              /*!< @brief Authentication scheme for downloading a the image over HTTP. */
#define OTA_JSON_FILETYPE_KEY           "fileType"                                                 /*!< @brief Used to identify the file in case of multi file type support. */
/** @} */

/**
 * @ingroup ota_private_enum_types
 * @brief Data ingest results.
 *
 * The negative error codes represent actual error in ingesting the data block whereas the positive error codes
 * represent success and other conditions that are not ingest errors like duplicate block is received.
 */
typedef enum
{
    IngestResultFileComplete = -1,     /*!< The file transfer is complete and the signature check passed. */
    IngestResultSigCheckFail = -2,     /*!< The file transfer is complete but the signature check failed. */
    IngestResultFileCloseFail = -3,    /*!< There was a problem trying to close the receive file. */
    IngestResultNullInput = -4,        /*!< One of the input pointers is NULL. */
    IngestResultBadFileHandle = -5,    /*!< The receive file pointer is invalid. */
    IngestResultUnexpectedBlock = -6,  /*!< We were asked to ingest a block but were not expecting one. */
    IngestResultBlockOutOfRange = -7,  /*!< The received block is out of the expected range. */
    IngestResultBadData = -8,          /*!< The data block from the server was malformed. */
    IngestResultWriteBlockFailed = -9, /*!< The PAL layer failed to write the file block. */
    IngestResultNoDecodeMemory = -10,  /*!< Memory could not be allocated for decoding . */
    IngestResultUninitialized = -127,  /*!< Software BUG: We forgot to set the result code. */
    IngestResultAccepted_Continue = 0, /*!< The block was accepted and we're expecting more. */
    IngestResultDuplicate_Continue = 1 /*!< The block was a duplicate but that's OK. Continue. */
} IngestResult_t;

/**
 * @ingroup ota_private_enum_types
 * @brief Generic JSON document parser errors.
 *
 */
typedef enum
{
    DocParseErrUnknown = -1,          /*!< The error code has not yet been set by a logic path. */
    DocParseErrNone = 0,              /*!< No error in parsing the document. */
    DocParseErrOutOfMemory,           /*!< We failed to allocate enough dynamic memory for a field. */
    DocParseErrUserBufferInsuffcient, /*!< The supplied user buffer is insufficient for a field. */
    DocParseErrFieldTypeMismatch,     /*!< The field type parsed does not match the document model. */
    DocParseErrBase64Decode,          /*!< There was an error decoding the base64 data. */
    DocParseErrInvalidNumChar,        /*!< There was an invalid character in a numeric value field. */
    DocParseErrDuplicatesNotAllowed,  /*!< A duplicate parameter was found in the job document. */
    DocParseErrMalformedDoc,          /*!< The document didn't fulfill the model requirements. */
    DocParseErr_InvalidJSONBuffer,    /*!< When the JSON is malformed and not parsed correctly. */
    DocParseErrNullModelPointer,      /*!< The pointer to the document model was NULL. */
    DocParseErrNullBodyPointer,       /*!< The document model's internal body pointer was NULL. */
    DocParseErrNullDocPointer,        /*!< The pointer to the JSON document was NULL. */
    DocParseErrTooManyParams,         /*!< The document model has more parameters than we can handle. */
    DocParseErrParamKeyNotInModel,    /*!< The document model does not include the specified parameter key. */
    DocParseErrInvalidModelParamType, /*!< The document model specified an invalid parameter type. */
    DocParseErrInvalidToken           /*!< The Jasmine token was invalid, producing a NULL pointer. */
} DocParseErr_t;

/**
 * @ingroup ota_private_enum_types
 * @brief Document model parameter types used by the JSON document parser.
 *
 */
typedef enum
{
    ModelParamTypeStringCopy,
    ModelParamTypeStringInDoc, /* Only use this type if you can process before freeing the document memory. */
    ModelParamTypeObject,
    ModelParamTypeArray,
    ModelParamTypeUInt32,
    ModelParamTypeSigBase64,
    ModelParamTypeIdent,
    ModelParamTypeArrayCopy
} ModelParamType_t;

/**
 * @ingroup ota_private_enum_types
 * @brief Gives the reason to set for job parsing operation.
 *
 */
typedef enum
{
    JobReasonReceiving = 0,  /* Update progress status. */
    JobReasonSigCheckPassed, /* Set status details to Self Test Ready. */
    JobReasonSelfTestActive, /* Set status details to Self Test Active. */
    JobReasonAccepted,       /* Set job state to Succeeded. */
    JobReasonRejected,       /* Set job state to Failed. */
    JobReasonAborted,        /* Set job state to Failed. */
    NumJobReasons
} OtaJobReason_t;

/**
 * @ingroup ota_private_struct_types
 * @brief JSON document parameter to store the details of keys and where to store them.
 *
 * This is a document parameter structure used by the document model. It determines
 * the type of parameter specified by the key name and where to store the parameter
 * locally when it is extracted from the JSON document. It also contains the
 * expected Jasmine type of the value field for validation.
 *
 * @note The destOffset field is an offset into the models context structure.
 */
typedef struct
{
    const char * pSrcKey;                  /*!< Expected key name. */
    const bool required;                   /*!< If true, this parameter must exist in the document. */
    uint16_t pDestOffset;                  /*!< Offset to where we will store the value, if not ~0. */
    uint16_t pDestSizeOffset;              /*!< Offset to where we will store the value, if not ~0. */
    const ModelParamType_t modelParamType; /*!< We extract the value, if found, based on this type. */
} JsonDocParam_t;

/**
 * @ingroup ota_private_struct_types
 * @brief JSON document model to store the details of parameters expected in the job document.
 *
 * The document model is currently limited to 32 parameters per the implementation,
 * although it may be easily expanded to more in the future by simply expanding
 * the parameter bitmap.
 *
 * The document model is used to control what JSON parameters are expected from a
 * document and where to store the parameters, if desired, in a destination context.
 * We currently only store parameters into an OtaFileContext_t but it could be used
 * for any structure since we don't use a type pointer.
 */
typedef struct
{
    void * contextBase;              /*!< The base address of the destination OTA context structure. */
    uint32_t contextSize;            /*!< The size, in bytes, of the destination context structure. */
    const JsonDocParam_t * pBodyDef; /*!< Pointer to the document model body definition. */
    uint16_t numModelParams;         /*!< The number of entries in the document model (limited to 32). */
    uint32_t paramsReceivedBitmap;   /*!< Bitmap of the parameters received based on the model. */
    uint32_t paramsRequiredBitmap;   /*!< Bitmap of the parameters required from the model. */
} JsonDocModel_t;

/**
 * @ingroup ota_private_struct_types
 * @brief This is the OTA statistics structure to hold useful info.
 */
typedef struct OtaAgentStatistics
{
    uint32_t otaPacketsReceived;  /*!< Number of OTA packets received by the MQTT callback. */
    uint32_t otaPacketsQueued;    /*!< Number of OTA packets queued by the MQTT callback. */
    uint32_t otaPacketsProcessed; /*!< Number of OTA packets processed by the OTA task. */
    uint32_t otaPacketsDropped;   /*!< Number of OTA packets dropped due to congestion. */
} OtaAgentStatistics_t;

/**
 * @ingroup ota_enum_types
 * @brief OTA Image states.
 *
 * After an OTA update image is received and authenticated, it is logically moved to
 * the Self Test state by the OTA agent pending final acceptance. After the image is
 * activated and tested by your user code, you should put it into either the Accepted
 * or Rejected state by calling @ref OTA_SetImageState ( OtaImageStateAccepted ) or
 * @ref OTA_SetImageState ( OtaImageStateRejected ). If the image is accepted, it becomes
 * the main firmware image to be booted from then on. If it is rejected, the image is
 * no longer valid and shall not be used, reverting to the last known good image.
 *
 * If you want to abort an active OTA transfer, you may do so by calling the API
 * @ref OTA_SetImageState ( OtaImageStateAborted ).
 */
typedef enum OtaImageState
{
    OtaImageStateUnknown = 0,  /*!< @brief The initial state of the OTA MCU Image. */
    OtaImageStateTesting = 1,  /*!< @brief The state of the OTA MCU Image post successful download and reboot. */
    OtaImageStateAccepted = 2, /*!< @brief The state of the OTA MCU Image post successful download and successful self_test. */
    OtaImageStateRejected = 3, /*!< @brief The state of the OTA MCU Image when the job has been rejected. */
    OtaImageStateAborted = 4,  /*!< @brief The state of the OTA MCU Image after a timeout publish to the stream request fails.
                                *   Also if the OTA MCU image is aborted in the middle of a stream. */
    OtaLastImageState = OtaImageStateAborted
} OtaImageState_t;

/**
 * @ingroup ota_enum_types
 * @brief OTA Platform Image State.
 *
 * The image state set by platform implementation.
 */
typedef enum OtaPalImageState
{
    OtaPalImageStateUnknown = 0,   /*!< @brief The initial state of the OTA PAL Image. */
    OtaPalImageStatePendingCommit, /*!< @brief OTA PAL Image awaiting update. */
    OtaPalImageStateValid,         /*!< @brief OTA PAL Image is valid. */
    OtaPalImageStateInvalid        /*!< @brief OTA PAL Image is invalid. */
} OtaPalImageState_t;

/**
 * @ingroup ota_enum_types
 * @brief OTA Agent Events.
 *
 * The events sent to OTA agent.
 */
typedef enum OtaEvent
{
    OtaAgentEventStart = 0,           /*!< @brief Start the OTA state machine */
    OtaAgentEventStartSelfTest,       /*!< @brief Event to trigger self test. */
    OtaAgentEventRequestJobDocument,  /*!< @brief Event for requesting job document. */
    OtaAgentEventReceivedJobDocument, /*!< @brief Event when job document is received. */
    OtaAgentEventCreateFile,          /*!< @brief Event to create a file. */
    OtaAgentEventRequestFileBlock,    /*!< @brief Event to request file blocks. */
    OtaAgentEventReceivedFileBlock,   /*!< @brief Event to trigger when file block is received. */
    OtaAgentEventRequestTimer,        /*!< @brief Event to request event timer. */
    OtaAgentEventCloseFile,           /*!< @brief Event to trigger closing file. */
    OtaAgentEventSuspend,             /*!< @brief Event to suspend ota task */
    OtaAgentEventResume,              /*!< @brief Event to resume suspended task */
    OtaAgentEventUserAbort,           /*!< @brief Event triggered by user to stop agent. */
    OtaAgentEventShutdown,            /*!< @brief Event to trigger ota shutdown */
    OtaAgentEventMax                  /*!< @brief Last event specifier */
} OtaEvent_t;

/**
 * @ingroup ota_struct_types
 * @brief OTA File Signature info.
 *
 * File key signature information to verify the authenticity of the incoming file
 */
typedef struct
{
    uint16_t size;                         /*!< @brief Size, in bytes, of the signature. */
    uint8_t data[ kOTA_MaxSignatureSize ]; /*!< @brief The binary signature data. */
} Sig_t;

/**
 * @ingroup ota_struct_types
 * @brief OTA File Context Information.
 *
 * Information about an OTA Update file that is to be streamed. This structure is filled in from a
 * job notification MQTT message. Currently only one file context can be streamed at time.
 */
typedef struct OtaFileContext
{
    uint8_t * pFilePath;            /*!< @brief Update file pathname. */
    uint16_t filePathMaxSize;       /*!< @brief Maximum size of the update file path */
    otaconfigOTA_FILE_TYPE * pFile; /*!< @brief File type after file is open for write. */
    uint32_t fileSize;              /*!< @brief The size of the file in bytes. */
    uint32_t blocksRemaining;       /*!< @brief How many blocks remain to be received (a code optimization). */
    uint32_t fileAttributes;        /*!< @brief Flags specific to the file being received (e.g. secure, bundle, archive). */
    uint32_t serverFileID;          /*!< @brief The file is referenced by this numeric ID in the OTA job. */
    uint8_t * pJobName;             /*!< @brief The job name associated with this file from the job service. */
    uint16_t jobNameMaxSize;        /*!< @brief Maximum size of the job name. */
    uint8_t * pStreamName;          /*!< @brief The stream associated with this file from the OTA service. */
    uint16_t streamNameMaxSize;     /*!< @brief Maximum size of the stream name. */
    uint8_t * pRxBlockBitmap;       /*!< @brief Bitmap of blocks received (for deduplicating and missing block request). */
    uint16_t blockBitmapMaxSize;    /*!< @brief Maximum size of the block bitmap. */
    uint8_t * pCertFilepath;        /*!< @brief Pathname of the certificate file used to validate the receive file. */
    uint16_t certFilePathMaxSize;   /*!< @brief Maximum certificate path size. */
    uint8_t * pUpdateUrlPath;       /*!< @brief Url for the file. */
    uint16_t updateUrlMaxSize;      /*!< @brief Maximum size of the url. */
    uint8_t * pAuthScheme;          /*!< @brief Authorization scheme. */
    uint16_t authSchemeMaxSize;     /*!< @brief Maximum size of the auth scheme. */
    uint32_t updaterVersion;        /*!< @brief Used by OTA self-test detection, the version of Firmware that did the update. */
    bool isInSelfTest;              /*!< @brief True if the job is in self test mode. */
    uint8_t * pProtocols;           /*!< @brief Authorization scheme. */
    uint16_t protocolMaxSize;       /*!< @brief Maximum size of the  supported protocols string. */
    uint8_t * pDecodeMem;           /*!< @brief Decode memory. */
    uint32_t decodeMemMaxSize;      /*!< @brief Maximum size of the decode memory. */
    uint32_t fileType;              /*!< @brief The file type id set when creating the OTA job. */
    Sig_t * pSignature;             /*!< @brief Pointer to the file's signature structure. */
} OtaFileContext_t;

/**
 * @ingroup ota_private_struct_types
 * @brief  The OTA Agent event and data structures.
 */

typedef struct OtaEventData
{
    uint8_t data[ OTA_DATA_BLOCK_SIZE ]; /*!< Buffer for storing event information. */
    uint32_t dataLength;                 /*!< Total space required for the event. */
    bool bufferUsed;                     /*!< Flag set when buffer is used otherwise cleared. */
} OtaEventData_t;

/**
 * @ingroup ota_private_struct_types
 * @brief Stores information about the event message.
 *
 */
typedef struct OtaEventMsg
{
    OtaEventData_t * pEventData; /*!< Event status message. */
    OtaEvent_t eventId;          /*!< Identifier for the event. */
} OtaEventMsg_t;

/* *INDENT-OFF* */
#ifdef __cplusplus
    }
#endif
/* *INDENT-ON* */

#endif /* ifndef OTA_PRIVATE_H */
