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
 * @file ota_interface.c
 * @brief Internal interface for setting the data and control planes.
 */

/* Standard library includes. */
#include <string.h>
#include <assert.h>

/* OTA interface includes. */
#include "ota_interface_private.h"

/* OTA transport interface includes. */

#if ( configENABLED_DATA_PROTOCOLS & OTA_DATA_OVER_MQTT ) || ( configENABLED_CONTROL_PROTOCOL & OTA_CONTROL_OVER_MQTT )
    #include "ota_mqtt_private.h"
#endif

#if ( configENABLED_DATA_PROTOCOLS & OTA_DATA_OVER_HTTP )
    #include "ota_http_private.h"
#endif

/* Check for invalid data interface configurations. */

#if !( configENABLED_DATA_PROTOCOLS & configOTA_PRIMARY_DATA_PROTOCOL )
    #error "Primary data protocol must be enabled in the OTA configuration file."
#endif

#if !( ( configENABLED_DATA_PROTOCOLS & OTA_DATA_OVER_MQTT ) | ( configENABLED_DATA_PROTOCOLS & OTA_DATA_OVER_HTTP ) )
    #error "One or more of the data protocols must be set with configENABLED_DATA_PROTOCOLS."
#endif

#if !( ( configOTA_PRIMARY_DATA_PROTOCOL & OTA_DATA_OVER_MQTT ) | ( configOTA_PRIMARY_DATA_PROTOCOL & OTA_DATA_OVER_HTTP ) )
    #error "configOTA_PRIMARY_DATA_PROTOCOL must be set to OTA_DATA_OVER_MQTT or OTA_DATA_OVER_HTTP."
#endif

#if ( configOTA_PRIMARY_DATA_PROTOCOL >= ( OTA_DATA_OVER_MQTT | OTA_DATA_OVER_HTTP ) )
    #error "Invalid value for configOTA_PRIMARY_DATA_PROTOCOL: Value is expected to be OTA_DATA_OVER_MQTT or OTA_DATA_OVER_HTTP."
#endif

void setControlInterface( OtaControlInterface_t * pControlInterface )
{
    assert( pControlInterface != NULL );

    #if ( configENABLED_CONTROL_PROTOCOL == OTA_CONTROL_OVER_MQTT )
        pControlInterface->requestJob = requestJob_Mqtt;
        pControlInterface->updateJobStatus = updateJobStatus_Mqtt;
        pControlInterface->cleanup = cleanupControl_Mqtt;
    #else
    #error "Enable MQTT control as control operations are only supported over MQTT."
    #endif
}

OtaErr_t setDataInterface( OtaDataInterface_t * pDataInterface,
                           const uint8_t * pProtocol )
{
    OtaErr_t err = OtaErrInvalidDataProtocol;
    bool httpInJobDoc;
    bool mqttInJobDoc;

    httpInJobDoc = ( strstr( ( const char * ) pProtocol, "\"HTTP\"" ) != NULL ) ? true : false;
    mqttInJobDoc = ( strstr( ( const char * ) pProtocol, "\"MQTT\"" ) != NULL ) ? true : false;

    #if ( ( configENABLED_DATA_PROTOCOLS & OTA_DATA_OVER_MQTT ) && !( configENABLED_DATA_PROTOCOLS & OTA_DATA_OVER_HTTP ) )
        ( void ) httpInJobDoc;

        if( mqttInJobDoc == true )
        {
            pDataInterface->initFileTransfer = initFileTransfer_Mqtt;
            pDataInterface->requestFileBlock = requestFileBlock_Mqtt;
            pDataInterface->decodeFileBlock = decodeFileBlock_Mqtt;
            pDataInterface->cleanup = cleanupData_Mqtt;
            err = OtaErrNone;
        }
    #elif ( ( configENABLED_DATA_PROTOCOLS & OTA_DATA_OVER_HTTP ) && !( configENABLED_DATA_PROTOCOLS & OTA_DATA_OVER_MQTT ) )
        ( void ) mqttInJobDoc;

        if( httpInJobDoc == true )
        {
            pDataInterface->initFileTransfer = initFileTransfer_Http;
            pDataInterface->requestFileBlock = requestDataBlock_Http;
            pDataInterface->decodeFileBlock = decodeFileBlock_Http;
            pDataInterface->cleanup = cleanupData_Http;
            err = OtaErrNone;
        }
    #else /* if ( ( configENABLED_DATA_PROTOCOLS & OTA_DATA_OVER_MQTT ) && !( configENABLED_DATA_PROTOCOLS & OTA_DATA_OVER_HTTP ) ) */
        #if ( configOTA_PRIMARY_DATA_PROTOCOL == OTA_DATA_OVER_MQTT )
            if( mqttInJobDoc == true )
            {
                pDataInterface->initFileTransfer = initFileTransfer_Mqtt;
                pDataInterface->requestFileBlock = requestFileBlock_Mqtt;
                pDataInterface->decodeFileBlock = decodeFileBlock_Mqtt;
                pDataInterface->cleanup = cleanupData_Mqtt;
                err = OtaErrNone;
            }
            else if( httpInJobDoc == true )
            {
                pDataInterface->initFileTransfer = initFileTransfer_Http;
                pDataInterface->requestFileBlock = requestDataBlock_Http;
                pDataInterface->decodeFileBlock = decodeFileBlock_Http;
                pDataInterface->cleanup = cleanupData_Http;
                err = OtaErrNone;
            }
        #elif ( configOTA_PRIMARY_DATA_PROTOCOL == OTA_DATA_OVER_HTTP )
            if( httpInJobDoc == true )
            {
                pDataInterface->initFileTransfer = initFileTransfer_Http;
                pDataInterface->requestFileBlock = requestDataBlock_Http;
                pDataInterface->decodeFileBlock = decodeFileBlock_Http;
                pDataInterface->cleanup = cleanupData_Http;
                err = OtaErrNone;
            }
            else if( mqttInJobDoc == true )
            {
                pDataInterface->initFileTransfer = initFileTransfer_Mqtt;
                pDataInterface->requestFileBlock = requestFileBlock_Mqtt;
                pDataInterface->decodeFileBlock = decodeFileBlock_Mqtt;
                pDataInterface->cleanup = cleanupData_Mqtt;
                err = OtaErrNone;
            }
        #endif /* if ( configOTA_PRIMARY_DATA_PROTOCOL == OTA_DATA_OVER_MQTT ) */
    #endif /* if ( ( configENABLED_DATA_PROTOCOLS & OTA_DATA_OVER_MQTT ) && !( configENABLED_DATA_PROTOCOLS & OTA_DATA_OVER_HTTP ) ) */

    return err;
}
