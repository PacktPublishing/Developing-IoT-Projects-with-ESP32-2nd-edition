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
 * @file ota_config_defaults.h
 * @brief This represents the default values for the configuration macros
 * for the OTA library.
 *
 * @note This file SHOULD NOT be modified. If custom values are needed for
 * any configuration macro, an ota_config.h file should be provided to
 * the OTA library to override the default values defined in this file.
 * To use the custom config file, the OTA_DO_NOT_USE_CUSTOM_CONFIG preprocessor
 * macro SHOULD NOT be set.
 */

#ifndef OTA_CONFIG_DEFAULTS_H
#define OTA_CONFIG_DEFAULTS_H

/* *INDENT-OFF* */
#ifdef __cplusplus
    extern "C" {
#endif
/* *INDENT-ON* */

/* The macro definition for OTA_DO_NOT_USE_CUSTOM_CONFIG is for Doxygen
 * documentation only. */

/**
 * @brief Define this macro to build the OTA library without the custom config
 * file ota_config.h.
 *
 * Without the custom config, the OTA library builds with
 * default values of config macros defined in ota_config_defaults.h file.
 *
 * If a custom config is provided, then OTA_DO_NOT_USE_CUSTOM_CONFIG should not
 * be defined.
 */
#ifdef DOXYGEN
    #define OTA_DO_NOT_USE_CUSTOM_CONFIG
#endif

/**
 * @brief The number of words allocated to the stack for the OTA agent.
 *
 * The configuration parameter specifies the size of the stack that will be allocated
 * to the task being created (the size is specified in words, not bytes!). The amount
 * of stack required is dependent on the application specific parameters,
 * for more information [Link](https://www.freertos.org/FAQMem.html#StackSize)
 *
 * <b>Possible values:</b> Any positive 32 bit integer. <br>
 * <b>Default value:</b> Varies by platform
 */
#ifndef otaconfigSTACK_SIZE
    #define otaconfigSTACK_SIZE    "Please set otaconfigSTACK_SIZE"
#endif

/**
 * @brief The OTA agent task priority. Normally it runs at a low priority.
 *
 * For more information [Link](https://www.freertos.org/RTOS-task-priority.html).
 *
 * <b>Possible values:</b> 0 to ( configMAX_PRIORITIES - 1 ) <br>
 * <b>Default value:</b> Varies by platform.
 */
#ifndef otaconfigAGENT_PRIORITY
    #define otaconfigAGENT_PRIORITY    "Please set otaconfigAGENT_PRIORITY"
#endif

/**
 * @brief Log base 2 of the size of the file data block message (excluding the
 * header).
 *
 * <b>Possible values:</b> Any unsigned 32 integer. <br>
 * <b>Default value:</b> '12'
 */
#ifndef otaconfigLOG2_FILE_BLOCK_SIZE
    #define otaconfigLOG2_FILE_BLOCK_SIZE    12UL
#endif

/**
 * @brief Milliseconds to wait for the self test phase to succeed before we
 * force reset.
 *
 * <b>Possible values:</b> Any unsigned 32 integer. <br>
 * <b>Default value:</b> '16000'
 */
#ifndef otaconfigSELF_TEST_RESPONSE_WAIT_MS
    #define otaconfigSELF_TEST_RESPONSE_WAIT_MS    16000U
#endif

/**
 * @brief Milliseconds to wait before requesting data blocks from the OTA
 * service if nothing is happening.
 *
 * @note The wait timer is reset whenever a data block is received from the OTA
 * service so we will only send the request message after being idle for this
 * amount of time.
 *
 * <b>Possible values:</b> Any unsigned 32 integer. <br>
 * <b>Default value:</b> '10000'
 */
#ifndef otaconfigFILE_REQUEST_WAIT_MS
    #define otaconfigFILE_REQUEST_WAIT_MS    10000U
#endif

/**
 * @brief The maximum allowed length of the thing name used by the OTA agent.
 *
 * @note AWS IoT requires Thing names to be unique for each device that
 * connects to the broker. Likewise, the OTA agent requires the developer to
 * construct and pass in the Thing name when initializing the OTA agent. The
 * agent uses this size to allocate static storage for the Thing name used in
 * all OTA base topics. Namely $aws/things/thingName
 *
 * <b>Possible values:</b> Any unsigned 32 integer. <br>
 * <b>Default value:</b> '64'
 */
#ifndef otaconfigMAX_THINGNAME_LEN
    #define otaconfigMAX_THINGNAME_LEN    64U
#endif

/**
 * @brief The maximum number of data blocks requested from OTA streaming
 * service.
 *
 * @note This configuration parameter is sent with data requests and represents
 * the maximum number of data blocks the service will send in response. The
 * maximum limit for this must be calculated from the maximum data response
 * limit (128 KB from service) divided by the block size. For example if block
 * size is set as 1 KB then the maximum number of data blocks that we can
 * request is 128/1 = 128 blocks. Configure this parameter to this maximum
 * limit or lower based on how many data blocks response is expected for each
 * data requests.
 *
 * <b>Possible values:</b> Any unsigned 32 integer value greater than 0. <br>
 * <b>Default value:</b> '1'
 */
#ifndef otaconfigMAX_NUM_BLOCKS_REQUEST
    #define otaconfigMAX_NUM_BLOCKS_REQUEST    1U
#endif

/**
 * @brief The maximum number of requests allowed to send without a response
 * before we abort.
 *
 * @note This configuration parameter sets the maximum number of times the
 * requests are made over the selected communication channel before aborting
 * and returning error.
 *
 * <b>Possible values:</b> Any unsigned 32 integer. <br>
 * <b>Default value:</b> '32'
 */
#ifndef otaconfigMAX_NUM_REQUEST_MOMENTUM
    #define otaconfigMAX_NUM_REQUEST_MOMENTUM    32U
#endif

/**
 * @brief How frequently the device will report its OTA progress to the cloud.
 *
 * @note Device will update the job status with the number of blocks it has received every certain
 * number of blocks it receives. For example, 64 means device will update job status every 64 blocks
 * it receives.
 *
 * <b>Possible values:</b> Any unsigned 32 integer. <br>
 * <b>Default value:</b> '64'
 */
#ifndef otaconfigOTA_UPDATE_STATUS_FREQUENCY
    #define otaconfigOTA_UPDATE_STATUS_FREQUENCY    64U
#endif

/**
 * @brief The number of data buffers reserved by the OTA agent.
 *
 * @note This configurations parameter sets the maximum number of static data
 * buffers used by the OTA agent for job and file data blocks received.
 *
 * <b>Possible values:</b> Any unsigned 32 integer. <br>
 * <b>Default value:</b> '1'
 */
#ifndef otaconfigMAX_NUM_OTA_DATA_BUFFERS
    #define otaconfigMAX_NUM_OTA_DATA_BUFFERS    1U
#endif

/**
 * @brief Data type to represent a file.
 *
 * It is used to represent a file received via OTA. The file is declared as
 * the pointer of this type: otaconfigOTA_FILE_TYPE * pFile.
 *
 * <b>Possible values:</b> Any data type. <br>
 * <b>Default value:</b> FILE on Windows or Linux, uint8_t on other platforms.
 */
#ifndef otaconfigOTA_FILE_TYPE
    #if defined( WIN32 ) || defined( __linux__ )
        #define otaconfigOTA_FILE_TYPE    FILE
    #else
        #define otaconfigOTA_FILE_TYPE    uint8_t
    #endif
#endif

/**
 * @brief Flag to enable booting into updates that have an identical or lower
 * version than the current version.
 *
 * @note Set this configuration parameter to '1' to disable version checks.
 * This allows updates to an identical or lower version. This is provided for
 * testing purpose and it's recommended to always update to higher version and
 * keep this configuration disabled.
 *
 * <b>Possible values:</b> Any unsigned 32 integer. <br>
 * <b>Default value:</b> '0'
 */
#ifndef otaconfigAllowDowngrade
    #define otaconfigAllowDowngrade    0U
#endif

/**
 * @brief The file type id received in the job document.
 *
 * @note The file type id received in the job document that allows devices
 * to identify the type of file received from the cloud. This configuration
 * defines the file type id used for firmware updates. If this is changed
 * then the updated value must be used while creating firmware update jobs.
 *
 */
#ifndef configOTA_FIRMWARE_UPDATE_FILE_TYPE_ID
    #define configOTA_FIRMWARE_UPDATE_FILE_TYPE_ID    0U
#endif

/**
 * @brief The protocol selected for OTA control operations.
 *
 * @note This configurations parameter sets the default protocol for all the
 * OTA control operations like requesting OTA job, updating the job status etc.
 *
 * @note Only MQTT is supported at this time for control operations.
 *
 * <b>Possible values:</b> OTA_CONTROL_OVER_MQTT <br>
 * <b>Default value:</b> 'OTA_CONTROL_OVER_MQTT'
 */
#ifndef configENABLED_CONTROL_PROTOCOL
    #define configENABLED_CONTROL_PROTOCOL    ( OTA_CONTROL_OVER_MQTT )
#endif

/**
 * @brief The protocol selected for OTA data operations.
 *
 * @note This configurations parameter sets the protocols selected for the data
 * operations like requesting file blocks from the service.
 *
 * <b>Possible values:</b><br>
 * Enable data over MQTT - ( OTA_DATA_OVER_MQTT ) <br>
 * Enable data over HTTP - ( OTA_DATA_OVER_HTTP ) <br>
 * Enable data over both MQTT & HTTP - ( OTA_DATA_OVER_MQTT | OTA_DATA_OVER_HTTP ) <br>
 * <b>Default value:</b> 'OTA_DATA_OVER_MQTT'
 */
#ifndef configENABLED_DATA_PROTOCOLS
    #define configENABLED_DATA_PROTOCOLS    ( OTA_DATA_OVER_MQTT )
#endif

/**
 * @brief The preferred protocol selected for OTA data operations.
 *
 * @note Primary data protocol will be the protocol used for downloading file
 * if more than one protocol is selected while creating OTA job.
 *
 * <b>Possible values:</b><br>
 * Data over MQTT - ( OTA_DATA_OVER_MQTT ) <br>
 * Data over HTTP - ( OTA_DATA_OVER_HTTP ) <br>
 * <b>Default value:</b>  'OTA_DATA_OVER_MQTT'
 */
#ifndef configOTA_PRIMARY_DATA_PROTOCOL
    #define configOTA_PRIMARY_DATA_PROTOCOL    ( OTA_DATA_OVER_MQTT )
#endif

/**
 * @brief The polling timeout (milliseconds) to receive messages from event queue.
 *
 * <b>Possible values:</b> Any unsigned 32 integer. <br>
 * <b>Default value:</b> '1000'
 */
#ifndef configOTA_POLLING_EVENTS_TIMEOUT_MS
    #define configOTA_POLLING_EVENTS_TIMEOUT_MS    ( 1000U )
#endif

/**
 * @brief Macro that is called in the OTA library for logging "Error" level
 * messages.
 *
 * To enable error level logging in the OTA library, this macro should be
 * mapped to the application-specific logging implementation that supports
 * error logging.
 *
 * @note This logging macro is called in the OTA library with parameters
 * wrapped in double parentheses to be ISO C89/C90 standard compliant. For a
 * reference POSIX implementation of the logging macros, refer to the ota
 * default config file, and the logging-stack in demos folder of the
 * [AWS IoT Embedded C SDK repository](https://github.com/aws/aws-iot-device-sdk-embedded-C/tree/main).
 *
 * <b>Default value</b>: Error logging is turned off, and no code is generated
 * for calls to the macro in the OTA library on compilation.
 */
#ifndef LogError
    #define LogError( message )
#endif

/**
 * @brief Macro that is called in the OTA library for logging "Warning" level
 * messages.
 *
 * To enable warning level logging in the OTA library, this macro should be
 * mapped to the application-specific logging implementation that supports
 * warning logging.
 *
 * @note This logging macro is called in the OTA library with parameters
 * wrapped in double parentheses to be ISO C89/C90 standard compliant. For a
 * reference POSIX implementation of the logging macros, refer to the ota
 * default config file, and the logging-stack in demos folder of the
 * [AWS IoT Embedded C SDK repository](https://github.com/aws/aws-iot-device-sdk-embedded-C/tree/main).
 *
 * <b>Default value</b>: Warning logging is turned off, and no code is
 * generated for calls to the macro in the OTA library on compilation.
 */
#ifndef LogWarn
    #define LogWarn( message )
#endif

/**
 * @brief Macro that is called in the OTA library for logging "Info" level
 * messages.
 *
 * To enable info level logging in the OTA library, this macro should be
 * mapped to the application-specific logging implementation that supports
 * info logging.
 *
 * @note This logging macro is called in the OTA library with parameters
 * wrapped in double parentheses to be ISO C89/C90 standard compliant. For a
 * reference POSIX implementation of the logging macros, refer to the ota
 * default config file, and the logging-stack in demos folder of the
 * [AWS IoT Embedded C SDK repository](https://github.com/aws/aws-iot-device-sdk-embedded-C/tree/main).
 *
 * <b>Default value</b>: Info logging is turned off, and no code is
 * generated for calls to the macro in the OTA library on compilation.
 */
#ifndef LogInfo
    #define LogInfo( message )
#endif

/**
 * @brief Macro that is called in the OTA library for logging "Debug" level
 * messages.
 *
 * To enable Debug level logging in the OTA library, this macro should be
 * mapped to the application-specific logging implementation that supports
 * debug logging.
 *
 * @note This logging macro is called in the OTA library with parameters
 * wrapped in double parentheses to be ISO C89/C90 standard compliant. For a
 * reference POSIX implementation of the logging macros, refer to the ota
 * default config file, and the logging-stack in demos folder of the
 * [AWS IoT Embedded C SDK repository](https://github.com/aws/aws-iot-device-sdk-embedded-C/tree/main).
 *
 * <b>Default value</b>: Debug logging is turned off, and no code is
 * generated for calls to the macro in the OTA library on compilation.
 */
#ifndef LogDebug
    #define LogDebug( message )
#endif

/* *INDENT-OFF* */
#ifdef __cplusplus
    }
#endif
/* *INDENT-ON* */

#endif /* ifndef OTA_CONFIG_DEFAULTS_H */
