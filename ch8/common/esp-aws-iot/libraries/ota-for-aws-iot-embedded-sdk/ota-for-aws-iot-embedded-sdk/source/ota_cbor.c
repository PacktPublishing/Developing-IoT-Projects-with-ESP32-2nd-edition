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
 * @file ota_cbor.c
 * @brief CBOR encode/decode routines for AWS IoT Over-the-Air updates.
 */

#include <stdlib.h>
#include "cbor.h"
#include "ota_cbor_private.h"

/**
 * @brief Number of keys in cbor get stream request message.
 */
#define OTA_CBOR_GETSTREAMREQUEST_ITEM_COUNT    6

/* ========================================================================== */

/**
 * @brief Helper function to verify the data type of the value in map.
 *
 * @param[in] expectedType Data type expected.
 * @param[in] cborValue Value to check.
 * @return CborError
 */
static CborError checkDataType( CborType expectedType,
                                const CborValue * cborValue )
{
    CborError cborResult = CborNoError;
    CborType actualType = cbor_value_get_type( cborValue );

    if( actualType != expectedType )
    {
        cborResult = CborErrorIllegalType;
    }

    return cborResult;
}

/**
 * @brief Decode a Get Stream response message from AWS IoT OTA.
 *
 * @param[in] pMessageBuffer message to decode.
 * @param[in] messageSize size of the message to decode.
 * @param[out] pFileId Decoded file id value.
 * @param[out] pBlockId Decoded block id value.
 * @param[out] pBlockSize Decoded block size value.
 * @param[out] pPayload Buffer for the decoded payload.
 * @param[in,out] pPayloadSize maximum size of the buffer as in and actual
 * payload size for the decoded payload as out.
 *
 * @return TRUE when success, otherwise FALSE.
 */
bool OTA_CBOR_Decode_GetStreamResponseMessage( const uint8_t * pMessageBuffer,
                                               size_t messageSize,
                                               int32_t * pFileId,
                                               int32_t * pBlockId,
                                               int32_t * pBlockSize,
                                               uint8_t * const * pPayload,
                                               size_t * pPayloadSize )
{
    CborError cborResult = CborNoError;
    CborParser cborParser;
    CborValue cborValue, cborMap;
    size_t payloadSizeReceived = 0;

    if( ( pFileId == NULL ) ||
        ( pBlockId == NULL ) ||
        ( pBlockSize == NULL ) ||
        ( pPayload == NULL ) ||
        ( pPayloadSize == NULL ) ||
        ( pMessageBuffer == NULL ) )
    {
        cborResult = CborUnknownError;
    }

    /* Initialize the parser. */
    if( CborNoError == cborResult )
    {
        cborResult = cbor_parser_init( pMessageBuffer,
                                       messageSize,
                                       0,
                                       &cborParser,
                                       &cborMap );
    }

    /* Get the outer element and confirm that it's a "map," i.e., a set of
     * CBOR key/value pairs. */
    if( CborNoError == cborResult )
    {
        if( false == cbor_value_is_map( &cborMap ) )
        {
            cborResult = CborErrorIllegalType;
        }
    }

    /* Find the file ID. */
    if( CborNoError == cborResult )
    {
        cborResult = cbor_value_map_find_value( &cborMap,
                                                OTA_CBOR_FILEID_KEY,
                                                &cborValue );
    }

    if( CborNoError == cborResult )
    {
        cborResult = checkDataType( CborIntegerType, &cborValue );
    }

    if( CborNoError == cborResult )
    {
        cborResult = cbor_value_get_int( &cborValue,
                                         ( int32_t * ) pFileId );
    }

    /* Find the block ID. */
    if( CborNoError == cborResult )
    {
        cborResult = cbor_value_map_find_value( &cborMap,
                                                OTA_CBOR_BLOCKID_KEY,
                                                &cborValue );
    }

    if( CborNoError == cborResult )
    {
        cborResult = checkDataType( CborIntegerType, &cborValue );
    }

    if( CborNoError == cborResult )
    {
        cborResult = cbor_value_get_int( &cborValue,
                                         ( int32_t * ) pBlockId );
    }

    /* Find the block size. */
    if( CborNoError == cborResult )
    {
        cborResult = cbor_value_map_find_value( &cborMap,
                                                OTA_CBOR_BLOCKSIZE_KEY,
                                                &cborValue );
    }

    if( CborNoError == cborResult )
    {
        cborResult = checkDataType( CborIntegerType, &cborValue );
    }

    if( CborNoError == cborResult )
    {
        cborResult = cbor_value_get_int( &cborValue,
                                         ( int32_t * ) pBlockSize );
    }

    /* Find the payload bytes. */
    if( CborNoError == cborResult )
    {
        cborResult = cbor_value_map_find_value( &cborMap,
                                                OTA_CBOR_BLOCKPAYLOAD_KEY,
                                                &cborValue );
    }

    if( CborNoError == cborResult )
    {
        cborResult = checkDataType( CborByteStringType, &cborValue );
    }

    /* Calculate the size we need to malloc for the payload. */
    if( CborNoError == cborResult )
    {
        cborResult = cbor_value_calculate_string_length( &cborValue,
                                                         &payloadSizeReceived );
    }

    if( CborNoError == cborResult )
    {
        /* Check if the received payload size is less than or equal to buffer size. */
        if( payloadSizeReceived <= ( *pPayloadSize ) )
        {
            *pPayloadSize = payloadSizeReceived;
        }
        else
        {
            cborResult = CborErrorOutOfMemory;
        }
    }

    if( CborNoError == cborResult )
    {
        cborResult = cbor_value_copy_byte_string( &cborValue,
                                                  *pPayload,
                                                  pPayloadSize,
                                                  NULL );
    }

    return CborNoError == cborResult;
}

/**
 * @brief Create an encoded Get Stream Request message for the AWS IoT OTA
 * service. The service allows block count or block bitmap to be requested,
 * but not both.
 *
 * @param[in,out] pMessageBuffer Buffer to store the encoded message.
 * @param[in] messageBufferSize Size of the buffer to store the encoded message.
 * @param[out] pEncodedMessageSize Size of the final encoded message.
 * @param[in] pClientToken Client token in the encoded message.
 * @param[in] fileId Value of file id in the encoded message.
 * @param[in] blockSize Value of block size in the encoded message.
 * @param[in] blockOffset Value of block offset in the encoded message.
 * @param[in] pBlockBitmap bitmap in the encoded message.
 * @param[in] blockBitmapSize Size of the provided bitmap buffer.
 * @param[in] numOfBlocksRequested number of blocks to request in the encoded message.
 *
 * @return TRUE when success, otherwise FALSE.
 */
bool OTA_CBOR_Encode_GetStreamRequestMessage( uint8_t * pMessageBuffer,
                                              size_t messageBufferSize,
                                              size_t * pEncodedMessageSize,
                                              const char * pClientToken,
                                              int32_t fileId,
                                              int32_t blockSize,
                                              int32_t blockOffset,
                                              const uint8_t * pBlockBitmap,
                                              size_t blockBitmapSize,
                                              int32_t numOfBlocksRequested )
{
    CborError cborResult = CborNoError;
    CborEncoder cborEncoder, cborMapEncoder;

    if( ( pMessageBuffer == NULL ) ||
        ( pEncodedMessageSize == NULL ) ||
        ( pClientToken == NULL ) ||
        ( pBlockBitmap == NULL ) )
    {
        cborResult = CborUnknownError;
    }

    /* Initialize the CBOR encoder. */
    if( CborNoError == cborResult )
    {
        cbor_encoder_init( &cborEncoder,
                           pMessageBuffer,
                           messageBufferSize,
                           0 );
        cborResult = cbor_encoder_create_map( &cborEncoder,
                                              &cborMapEncoder,
                                              OTA_CBOR_GETSTREAMREQUEST_ITEM_COUNT );
    }

    /* Encode the client token key and value. */
    if( CborNoError == cborResult )
    {
        cborResult = cbor_encode_text_stringz( &cborMapEncoder,
                                               OTA_CBOR_CLIENTTOKEN_KEY );
    }

    if( CborNoError == cborResult )
    {
        cborResult = cbor_encode_text_stringz( &cborMapEncoder,
                                               pClientToken );
    }

    /* Encode the file ID key and value. */
    if( CborNoError == cborResult )
    {
        cborResult = cbor_encode_text_stringz( &cborMapEncoder,
                                               OTA_CBOR_FILEID_KEY );
    }

    if( CborNoError == cborResult )
    {
        cborResult = cbor_encode_int( &cborMapEncoder,
                                      fileId );
    }

    /* Encode the block size key and value. */
    if( CborNoError == cborResult )
    {
        cborResult = cbor_encode_text_stringz( &cborMapEncoder,
                                               OTA_CBOR_BLOCKSIZE_KEY );
    }

    if( CborNoError == cborResult )
    {
        cborResult = cbor_encode_int( &cborMapEncoder,
                                      blockSize );
    }

    /* Encode the block offset key and value. */
    if( CborNoError == cborResult )
    {
        cborResult = cbor_encode_text_stringz( &cborMapEncoder,
                                               OTA_CBOR_BLOCKOFFSET_KEY );
    }

    if( CborNoError == cborResult )
    {
        cborResult = cbor_encode_int( &cborMapEncoder,
                                      blockOffset );
    }

    /* Encode the block bitmap key and value. */
    if( CborNoError == cborResult )
    {
        cborResult = cbor_encode_text_stringz( &cborMapEncoder,
                                               OTA_CBOR_BLOCKBITMAP_KEY );
    }

    if( CborNoError == cborResult )
    {
        cborResult = cbor_encode_byte_string( &cborMapEncoder,
                                              pBlockBitmap,
                                              blockBitmapSize );
    }

    /* Encode the number of blocks requested key and value. */
    if( CborNoError == cborResult )
    {
        cborResult = cbor_encode_text_stringz( &cborMapEncoder,
                                               OTA_CBOR_NUMBEROFBLOCKS_KEY );
    }

    if( CborNoError == cborResult )
    {
        cborResult = cbor_encode_int( &cborMapEncoder,
                                      numOfBlocksRequested );
    }

    /* Close the encoder. */
    if( CborNoError == cborResult )
    {
        cborResult = cbor_encoder_close_container_checked( &cborEncoder,
                                                           &cborMapEncoder );
    }

    /* Get the encoded size. */
    if( CborNoError == cborResult )
    {
        *pEncodedMessageSize = cbor_encoder_get_buffer_size( &cborEncoder,
                                                             pMessageBuffer );
    }

    return CborNoError == cborResult;
}
