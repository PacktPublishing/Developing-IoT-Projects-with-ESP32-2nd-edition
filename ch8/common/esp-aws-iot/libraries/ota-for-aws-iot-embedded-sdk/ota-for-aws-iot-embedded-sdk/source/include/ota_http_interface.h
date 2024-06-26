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
 * @file ota_http_interface.h
 * @brief Contains OTA HTTP Statuses, function type definitions and http interface structure.
 */

#ifndef OTA_HTTP_INTERFACE_H
#define OTA_HTTP_INTERFACE_H

/* *INDENT-OFF* */
#ifdef __cplusplus
    extern "C" {
#endif
/* *INDENT-ON* */

/* Standard library includes. */
#include <stddef.h>
#include <stdint.h>

/**
 * @otahttppage
 * @brief The OTA PAL interface definition.
 *
 * @otahttpsectionoverview
 *
 * The OTA MQTT interface is a set of APIs that must be implemented by
 * a library to enable the OTA library to download a file block by
 * connecting to a pre-signed url and fetching data blocks.
 *
 * The OTA MQTT interface is defined in @ref ota_mqtt_interface.h.
 * <br>
 *
 * The functions that must be implemented are:<br>
 * - [OTA MQTT Subscribe](@ref OtaMqttSubscribe_t)
 * - [OTA MQTT Unsubscribe](@ref OtaMqttSubscribe_t)
 * - [OTA MQTT Publish](@ref OtaMqttSubscribe_t)
 *
 * These functions can be grouped into the structure `OtaHttpInterface_t`
 * and passed to @ref OtaInterfaces_t to represent the MQTT interface.
 * @code{c}
 * OtaHttpInterface_t httpInterface;
 * httpInterface.init = httpInit;
 * httpInterface.request = httpRequest;
 * httpInterface.deinit = httpDeinit;
 *
 *  .....
 *
 * OtaInterfaces_t otaInterfaces;
 * otaInterfaces.http = httpInterface
 *
 *  .....
 *
 * OTA_Init( &otaBuffer,
 *           &otaInterfaces,
 *           ( CLIENT_IDENTIFIER ),
 *           otaAppCallback )
 * @endcode
 */

/**
 * @ingroup ota_enum_types
 * @brief The OTA HTTP interface return status.
 */
typedef enum OtaHttpStatus
{
    OtaHttpSuccess = 0,       /*!< @brief OTA HTTP interface success. */
    OtaHttpInitFailed = 0xc0, /*!< @brief Error initializing the HTTP connection. */
    OtaHttpDeinitFailed,      /*!< @brief Error deinitializing the HTTP connection. */
    OtaHttpRequestFailed      /*!< @brief Error sending the HTTP request. */
} OtaHttpStatus_t;

/**
 * @brief Init OTA Http interface.
 *
 * This function parses the pre-signed url and initializes connection.
 *
 * @param[in] pUrl         Pointer to the pre-signed url for downloading update file.
 *
 * @return              OtaHttpSuccess if success , other error code on failure.
 */

typedef OtaHttpStatus_t ( * OtaHttpInit_t ) ( char * pUrl );

/**
 * @brief Request file block over Http.
 *
 * This function requests file block over Http from the rangeStart and rangeEnd.
 *
 * @param[in] rangeStart  Starting index of the file data to be requested.
 *
 * @param[in] rangeEnd    End index of the file data to be requested.
 *
 * @return             OtaHttpSuccess if success , other error code on failure.
 */

typedef OtaHttpStatus_t ( * OtaHttpRequest_t )  ( uint32_t rangeStart,
                                                  uint32_t rangeEnd );

/**
 * @brief Deinit OTA Http interface.
 *
 * This function cleanups Http connection and other data used for
 * requesting file blocks using the pre-signed url.
 *
 * @return        OtaHttpSuccess if success , other error code on failure.
 */
typedef OtaHttpStatus_t ( * OtaHttpDeinit )( void );

/**
 * @ingroup ota_struct_types
 * @brief OTA Event Interface structure.
 *
 */
typedef struct OtaHttpInterface
{
    OtaHttpInit_t init;       /*!< @brief Reference to HTTP initialization. */
    OtaHttpRequest_t request; /*!< @brief Reference to HTTP data request. */
    OtaHttpDeinit deinit;     /*!< @brief Reference to HTTP deinitialize. */
} OtaHttpInterface_t;

/* *INDENT-OFF* */
#ifdef __cplusplus
    }
#endif
/* *INDENT-ON* */

#endif /* ifndef OTA_HTTP_INTERFACE_H */
