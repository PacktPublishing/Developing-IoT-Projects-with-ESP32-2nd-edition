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
 * @file OTA_Init_harness.c
 * @brief Implements the proof harness for OTA_Init function.
 */
/* Include headers for ota agent. */
#include "ota.h"
#include <stdlib.h>

OtaOsStatus_t init( OtaEventContext_t * pEventCtx )
{
    OtaOsStatus_t status;

    return status;
}

void OTA_Init_harness()
{
    OtaErr_t err;
    OtaAppBuffer_t otaBuffer;
    OtaInterfaces_t otaInterface;
    uint8_t * pThingName;
    OtaAppCallback_t otaAppCallback;
    size_t size;

    /* Initialize the function pointer to a stub. */
    otaInterface.os.event.init = init;

    /* The maximum size of a valid name of a thing is defined by otaconfigMAX_THINGNAME_LEN. The upper bound
     * of size is selected to consider the cases where size of the string is greater than maximum value. */
    __CPROVER_assume( size > 0 && size <= otaconfigMAX_THINGNAME_LEN + 1 );

    pThingName = ( uint8_t * ) malloc( sizeof( uint8_t ) * size );

    /* pThingName is a string and should end with a NULL character. */
    if( pThingName != NULL )
    {
        pThingName[ size - 1 ] = '\0';
    }

    err = OTA_Init( &otaBuffer, &otaInterface, pThingName, otaAppCallback );

    /* OTA_Init must always return either OtaErrNone or OtaErrUninitialized. */
    __CPROVER_assert( ( err == OtaErrNone ) || ( err == OtaErrUninitialized ), "Invalid Return value: Expected OtaErrNone" );

    free( pThingName );
}
