/*
 * AWS IoT Over-the-air Update v3.4.0
 * Copyright (C) 2021 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * @file prvBuildStatusMessageFinish_harness.c
 * @brief Implements the proof harness for prvBuildStatusMessageFinish function.
 */
/* Include headers for mqtt interface. */
#include "ota_mqtt_private.h"

#define OTA_STATUS_MSG_MAX_SIZE    128U                 /*!< Max length of a job status message to the service. */

uint32_t __CPROVER_file_local_ota_mqtt_c_prvBuildStatusMessageFinish( char * pMsgBuffer,
                                                                      size_t msgBufferSize,
                                                                      OtaJobStatus_t status,
                                                                      int32_t reason,
                                                                      int32_t subReason,
                                                                      uint32_t previousVersion );

/* Stub required to populate and generate strings for testing the function. */
size_t __CPROVER_file_local_ota_mqtt_c_stringBuilder( char * pBuffer,
                                                      size_t bufferSizeBytes,
                                                      const char * strings[] )
{
    size_t stringSize;

    /* pBuffer is initialized in updateJobStatus_Mqtt function before passing it to the
    * stringBuilder function in prvBuildStatusMessageFinish and thus cannot be NULL. */
    __CPROVER_assert( pBuffer != NULL,
                      "Unable to use pBuffer: passed pointer value is NULL." );

    /* strings is initialized prvBuildStatusMessageFinish function before passing it to the
     * stringBuilder function and thus cannot be NULL. */
    __CPROVER_assert( strings != NULL,
                      "Unable to use strings: passed pointer value is NULL." );

    /* The static size of the pBuffer in the updateJobStatus_Mqtt function is
     * defined by bufferSizeBytes. Hence, the value stringSize can
     * never exceed bufferSizeBytes. */
    __CPROVER_assume( stringSize > 0U && stringSize < bufferSizeBytes );

    return stringSize;
}
/* Stub required to convert a hexadecimal number into a string. */
size_t __CPROVER_file_local_ota_mqtt_c_stringBuilderUInt32Hex( char * pBuffer,
                                                               size_t bufferSizeBytes,
                                                               uint32_t value )
{
    size_t buffersize;

    return buffersize;
}

/* Stub required to convert a decimal number into a string. */
size_t __CPROVER_file_local_ota_mqtt_c_stringBuilderUInt32Decimal( char * pBuffer,
                                                                   size_t bufferSizeBytes,
                                                                   uint32_t value )
{
    size_t buffersize;

    return buffersize;
}

/*****************************************************************************/
void prvBuildStatusMessageFinish_harness()
{
    uint32_t msgSize;
    OtaJobStatus_t status;
    int32_t reason;
    int32_t subReason;
    uint32_t previousVersion;

    /* The pMsg if statically defined in the updateJobStatus_Mqtt with its size
     * defined by OTA_STATUS_MSG_MAX_SIZE.*/
    char pMsg[ OTA_STATUS_MSG_MAX_SIZE ];

    msgSize = OTA_STATUS_MSG_MAX_SIZE;

    /* The prvBuildStatusMessageFinish function is only called when status
     * is not equal to JobStatusInProgress and the value is less than NumJobStatusMappings. */
    __CPROVER_assume( status > 0 && status < NumJobStatusMappings );

    /* reason is of OtaJobReason_t datatype it follows the values ranging from 0 to 6.*/
    __CPROVER_assume( reason >= 0 && reason < 6 );

    /* previousVersion is typecasted to int32_t and expects values less than INT32_MAX. */
    __CPROVER_assume( previousVersion < INT32_MAX );

    /* subReason is typecasted to uint32_t and expects values greater than 0. */
    __CPROVER_assume( subReason > 0 );

    ( void ) __CPROVER_file_local_ota_mqtt_c_prvBuildStatusMessageFinish( pMsg, msgSize, status, reason, subReason, previousVersion );
}
