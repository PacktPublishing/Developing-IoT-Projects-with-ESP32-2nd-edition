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
 * @file OTA_CBOR_Decode_GetStreamResponseMessage_harness.c
 * @brief Implements the proof harness for OTA_CBOR_Decode_GetStreamResponseMessage function.
 */
/* Include headers for cbor parsing. */
#include "cbor.h"
#include "ota_cbor_private.h"

/* Stub to return CBORerror type. */
CborError returnCborError()
{
    CborError err;

    return err;
}

/* Stub to initialize the cbor parser. */
CborError cbor_parser_init( const uint8_t * buffer,
                            size_t size,
                            uint32_t flags,
                            CborParser * parser,
                            CborValue * it )
{
    return returnCborError();
}

/* Stub to map the value with CborMapType. */
bool __CPROVER_file_local_cbor_h_cbor_value_is_map( const CborValue * value )
{
    return value->type == CborMapType;
}

/* Stub to find the value in map. */
CborError cbor_value_map_find_value( const CborValue * map,
                                     const char * string,
                                     CborValue * element )
{
    return returnCborError();
}

/* Stub to check the datatype of the value. */
CborError __CPROVER_file_local_ota_cbor_c_checkDataType( CborType expectedType,
                                                         CborValue * cborValue )
{
    return returnCborError();
}

/* Stub to get the integer from cborvalue. */
CborError __CPROVER_file_local_cbor_h_cbor_value_get_int( const CborValue * value,
                                                          int * result )
{
    return returnCborError();
}

/* Stub to calculate the string length that value points at and store it in len. */
CborError cbor_value_calculate_string_length( const CborValue * value,
                                              size_t * len )
{
    size_t stringSize;

    *len = stringSize;

    return returnCborError();
}

/* Stub to copy the byte string to the buffer. */
CborError __CPROVER_file_local_cbor_h_cbor_value_copy_byte_string( const CborValue * value,
                                                                   uint8_t * buffer,
                                                                   size_t * buflen,
                                                                   CborValue * next )
{
    return returnCborError();
}

void OTA_CBOR_Decode_GetStreamResponseMessage_harness()
{
    uint8_t * pMessageBuffer;
    size_t messageSize;
    int32_t * pFileId;
    int32_t * pBlockId;
    int32_t * pBlockSize;
    uint8_t ** pPayload;
    size_t * pPayloadSize;

    /* Allocating memory to the variables. Since malloc can fail this also covers cases where
     * the variables are pointing at NULL. */
    pMessageBuffer = ( uint8_t * ) malloc( messageSize );
    pFileId = ( int32_t * ) malloc( sizeof( uint32_t ) );
    pBlockId = ( int32_t * ) malloc( sizeof( uint32_t ) );
    pBlockSize = ( int32_t * ) malloc( sizeof( int32_t ) );
    pPayloadSize = ( size_t * ) malloc( sizeof( size_t ) );
    pPayload = ( uint8_t ** ) malloc( sizeof( uint8_t * ) );

    if( pPayload != NULL )
    {
        *pPayload = ( uint8_t * ) malloc( sizeof( uint8_t ) );
    }

    OTA_CBOR_Decode_GetStreamResponseMessage( pMessageBuffer, messageSize, pFileId, pBlockId, pBlockSize, pPayload, pPayloadSize );

    free( pMessageBuffer );
    free( pFileId );
    free( pBlockId );
    free( pBlockSize );
    free( pPayloadSize );

    if( pPayload != NULL )
    {
        free( *pPayload );
    }

    free( pPayload );
}
