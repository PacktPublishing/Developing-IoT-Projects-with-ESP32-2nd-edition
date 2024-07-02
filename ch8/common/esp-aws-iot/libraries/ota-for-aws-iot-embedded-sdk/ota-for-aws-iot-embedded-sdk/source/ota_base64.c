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
 * @file ota_base64.c
 * @brief Implements a Base64 decoding routine.
 */

#include "ota_base64_private.h"
#include <assert.h>

/**
 * @brief Number to represent both line feed and carriage return symbols in the
 *        pBase64SymbolToIndexMap table.
 */
#define NEWLINE                                  64U

/**
 * @brief Number to represent the whitespace character in the pBase64SymbolToIndexMap table.
 */
#define WHITESPACE                               65U

/**
 * @brief Number to represent the Base64 padding symbol in the pBase64SymbolToIndexMap table.
 */
#define PADDING_SYMBOL                           66U

/**
 * @brief Number to represent values that are invalid in the pBase64SymbolToIndexMap table.
 */
#define NON_BASE64_INDEX                         67U

/**
 * @brief Maximum value for a Base64 index that represents a valid, non-formatting Base64 symbol.
 */
#define VALID_BASE64_SYMBOL_INDEX_RANGE_MAX      63U

/**
 * @brief Number of bits in a sextet.
 */
#define SEXTET_SIZE                              6

/**
 * @brief Maximum number of Base64 symbols to store in a buffer before decoding them.
 */
#define MAX_NUM_BASE64_DATA                      4U

/**
 * @brief Maximum number of padding symbols in a string of encoded data that is considered valid.
 */
#define MAX_EXPECTED_NUM_PADDING                 2

/**
 * @brief Smallest amount of data that can be Base64 encoded is a byte. Encoding a single byte of
 *        data results in 2 bytes of encoded data. Therefore if the encoded data is smaller than 2
 *        bytes, there is an error with the data.
 */
#define MIN_VALID_ENCODED_DATA_SIZE              2U

/**
 * @brief The number of bits in a single octet.
 */
#define SIZE_OF_ONE_OCTET                        8U

/**
 * @brief The number of bits in two octets.
 */
#define SIZE_OF_TWO_OCTETS                       16U

/**
 * @brief The number of padding bits that are present when there are two sextets of encoded data.
 */
#define SIZE_OF_PADDING_WITH_TWO_SEXTETS         4

/**
 * @brief The number of padding bits that are present when there are three sextets of encoded data.
 */
#define SIZE_OF_PADDING_WITH_THREE_SEXTETS       2

/**
 * @brief Inclusive upper bound for valid values that can be contained in pBase64SymbolToIndexMap.
 */
#define SYMBOL_TO_INDEX_MAP_VALUE_UPPER_BOUND    67U

/**
 * @brief Inclusive upper bound for the range of valid Base64 index values.
 */
#define BASE64_INDEX_VALUE_UPPER_BOUND           63U

/**
 * @brief This table takes is indexed by an Ascii character and returns the respective Base64 index.
 *        The Ascii character used to index into this table is assumed to represent a symbol in a
 *        string of Base64 encoded data. There are three kinds of possible ascii characters:
 *        1) Base64 Symbols. These are the digits of a Base 64 number system.
 *        2) Formatting characters. These are newline, whitespace, and padding.
 *        3) Symbols that are impossible to have inside of correctly Base64 encoded data.
 *
 *        This table assumes that the padding symbol is the Ascii character '='
 *
 *        Valid Base64 symbols will have an index ranging from 0-63. The Base64 digits being used
 *        are "ABCDEFGHIJKLMNOPQRSTUVWXYabcdefghijklmnopqrstuvwxyz0123456789+/" where 'A' is the
 *        0th index of the Base64 symbols and '/' is the 63rd index.
 *
 *        Outside of the numbers 0-63, there are magic numbers in this table:
 *        - The 11th entry in this table has the number 64. This is to identify the ascii character
 *          '\n' as a newline character.
 *        - The 14th entry in this table has the number 64. This is to identify the ascii character
 *          '\\r' as a newline character.
 *        - The 33rd entry in this table has the number 65. This is to identify the ascii character
 *          ' ' as a whitespace character.
 *        - The 62nd entry in this table has the number 66. This is to identify the ascii character
 *          '=' as the padding character.
 *        - All positions in the ascii table that are invalid symbols are identified with the
 *          number 67 (other than '\n','\\r',' ','=').
 */
static const uint8_t pBase64SymbolToIndexMap[] =
{
    67, 67, 67, 67, 67, 67, 67, 67, 67, 67,
    64, 67, 67, 64, 67, 67, 67, 67, 67, 67,
    67, 67, 67, 67, 67, 67, 67, 67, 67, 67,
    67, 67, 65, 67, 67, 67, 67, 67, 67, 67,
    67, 67, 67, 62, 67, 67, 67, 63, 52, 53,
    54, 55, 56, 57, 58, 59, 60, 61, 67, 67,
    67, 66, 67, 67, 67, 0,  1,  2,  3,  4,
    5,  6,  7,  8,  9,  10, 11, 12, 13, 14,
    15, 16, 17, 18, 19, 20, 21, 22, 23, 24,
    25, 67, 67, 67, 67, 67, 67, 26, 27, 28,
    29, 30, 31, 32, 33, 34, 35, 36, 37, 38,
    39, 40, 41, 42, 43, 44, 45, 46, 47, 48,
    49, 50, 51, 67, 67, 67, 67, 67, 67, 67,
    67, 67, 67, 67, 67, 67, 67, 67, 67, 67,
    67, 67, 67, 67, 67, 67, 67, 67, 67, 67,
    67, 67, 67, 67, 67, 67, 67, 67, 67, 67,
    67, 67, 67, 67, 67, 67, 67, 67, 67, 67,
    67, 67, 67, 67, 67, 67, 67, 67, 67, 67,
    67, 67, 67, 67, 67, 67, 67, 67, 67, 67,
    67, 67, 67, 67, 67, 67, 67, 67, 67, 67,
    67, 67, 67, 67, 67, 67, 67, 67, 67, 67,
    67, 67, 67, 67, 67, 67, 67, 67, 67, 67,
    67, 67, 67, 67, 67, 67, 67, 67, 67, 67,
    67, 67, 67, 67, 67, 67, 67, 67, 67, 67,
    67, 67, 67, 67, 67, 67, 67, 67, 67, 67,
    67, 67, 67, 67, 67, 67
};

/**
 * @brief         Validates the input Base64 index based on the context of what
 *                has been decoded so far and the value of the index. Updates
 *                the input counters that are used to keep track of the number
 *                of whitespace and padding symbols that have been parsed so
 *                far.
 *
 * @param[in]     base64Index Base64 index that can have on of the values
 *                listed in pBase64SymbolToIndexMap. This index represents the
 *                value of a valid Base64 symbol, a number to identify it as a
 *                formatting symbol, or a number to identify it as an invalid
 *                symbol.
 * @param[in,out] pNumPadding Pointer to the number of padding symbols that are
 *                present before the input Base64 index in the encoded data.
 *                This number is incremented if the input symbol is a padding
 *                symbol.
 * @param[in,out] pNumWhitespace Pointer to the number of whitespace symbols
 *                that are present before the input Base64 index in the encoded
 *                data. This number is incremented if the input symbol is a
 *                whitespace symbol.
 *
 * @return        One of the following:
 *                - #Base64Success if the Base64 encoded data was valid
 *                  and successfully decoded.
 *                - An error code defined in ota_base64_private.h if the
 *                  encoded data or input parameters are invalid.
 */
static Base64Status_t preprocessBase64Index( uint8_t base64Index,
                                             int64_t * pNumPadding,
                                             int64_t * pNumWhitespace )
{
    Base64Status_t returnVal = Base64Success;
    int64_t numPadding;
    int64_t numWhitespace;

    assert( pNumPadding != NULL );
    assert( pNumWhitespace != NULL );

    numPadding = *pNumPadding;
    numWhitespace = *pNumWhitespace;

    /* Validate that the Base64 index is valid and in an appropriate place. */
    if( base64Index == NON_BASE64_INDEX )
    {
        returnVal = Base64InvalidSymbol;
    }
    else if( base64Index == PADDING_SYMBOL )
    {
        if( numWhitespace != 0 )
        {
            returnVal = Base64InvalidSymbolOrdering;
        }
        else if( ++numPadding > MAX_EXPECTED_NUM_PADDING )
        {
            returnVal = Base64InvalidPaddingSymbol;
        }
        else
        {
            /* No action required. */
        }
    }
    else if( base64Index == WHITESPACE )
    {
        ++numWhitespace;
    }
    else if( base64Index == NEWLINE )
    {
        /* No action required. */
    }

    /* In this case, the input is valid because the value of its index is inclusively between 0
     * and 63. Check that there was not a whitespace or padding symbol before this valid index. */
    else
    {
        assert( base64Index <= BASE64_INDEX_VALUE_UPPER_BOUND );

        if( ( numWhitespace != 0 ) || ( numPadding != 0 ) )
        {
            returnVal = Base64InvalidSymbolOrdering;
        }
    }

    *pNumWhitespace = numWhitespace;
    *pNumPadding = numPadding;
    return returnVal;
}

/**
 * @brief         Add a Base64 index to a Base64 index buffer. The buffer will
 *                only be updated if the index represents a Base64 digit.
 *
 * @param[in]     base64Index Base64 index that can have one of the values
 *                listed in pBase64SymbolToIndexMap.
 * @param[in,out] pBase64IndexBuffer Pointer to a 32 bit variable that contains
 *                Base64 indexes that will be decoded.
 * @param[in,out] pNumDataInBuffer Pointer to the number of sextets that are
 *                stored in pBase64IndexBuffer. This will be incremented if
 *                base64Index is stored in pBase64IndexBuffer.
 */
static void updateBase64DecodingBuffer( const uint8_t base64Index,
                                        uint32_t * pBase64IndexBuffer,
                                        uint32_t * pNumDataInBuffer )
{
    uint32_t base64IndexBuffer;
    uint32_t numDataInBuffer;

    assert( pBase64IndexBuffer != NULL );
    assert( pNumDataInBuffer != NULL );
    assert( base64Index <= SYMBOL_TO_INDEX_MAP_VALUE_UPPER_BOUND );

    base64IndexBuffer = *pBase64IndexBuffer;
    numDataInBuffer = *pNumDataInBuffer;

    /* Only update the buffer if the Base64 index is representing a Base64 digit. Base64 digits
     * have a Base64 index that is inclusively between 0 and 63. */
    if( base64Index <= VALID_BASE64_SYMBOL_INDEX_RANGE_MAX )
    {
        /* Shift the previously stored data over to make room for the next Base64 sextet and
         * store the current Base64 index that is represented by the 6 least significant bits.
         * Six is the number of bits you need to represent a character in Base64 (log2(64) = 6).
         * The remaining two most significant bits will always be 0 since the only valid range of
         * input data is between 0 and 63. */
        base64IndexBuffer = ( base64IndexBuffer << SEXTET_SIZE ) | base64Index;
        ++numDataInBuffer;
    }

    *pBase64IndexBuffer = base64IndexBuffer;
    *pNumDataInBuffer = numDataInBuffer;
}

/**
 * @brief         Decode a buffer containing two, three, or four Base64
 *                indices.
 *
 * @param[in,out] pBase64IndexBuffer Pointer to a 32 bit variable that contains
 *                Base64 indexes that will be decoded. Each index is
 *                represented by a sextet in the buffer.
 * @param[in,out] pNumDataInBuffer Pointer to the number of sextets (indexes)
 *                that are concatenated and stored in pBase64IndexBuffer. This
 *                will be set to zero before this function returns.
 * @param[out]    pDest Pointer to a buffer used for storing the decoded data.
 * @param[in]     destLen Length of the pDest buffer.
 * @param[in,out] pOutputLen Pointer to the index of pDest where the output
 *                should be written.
 *
 * @return        One of the following:
 *                - #Base64Success if the Base64 encoded data was valid
 *                  and successfully decoded.
 *                - An error code defined in ota_base64_private.h if the
 *                  encoded data or input parameters are invalid.
 */
static Base64Status_t decodeBase64IndexBuffer( uint32_t * pBase64IndexBuffer,
                                               uint32_t * pNumDataInBuffer,
                                               uint8_t * pDest,
                                               const size_t destLen,
                                               size_t * pOutputLen )
{
    Base64Status_t returnVal = Base64Success;
    size_t outputLen;
    uint32_t base64IndexBuffer;
    uint32_t numDataInBuffer;
    uint32_t numDataToWrite;

    assert( pBase64IndexBuffer != NULL );
    assert( pNumDataInBuffer != NULL );
    assert( ( *pNumDataInBuffer == 2U ) ||
            ( *pNumDataInBuffer == 3U ) ||
            ( *pNumDataInBuffer == 4U ) );
    assert( pDest != NULL );
    assert( pOutputLen != NULL );

    outputLen = *pOutputLen;
    base64IndexBuffer = *pBase64IndexBuffer;
    numDataInBuffer = *pNumDataInBuffer;
    numDataToWrite = ( numDataInBuffer * 3U ) / 4U;

    if( destLen < ( outputLen + numDataToWrite ) )
    {
        returnVal = Base64InvalidBufferSize;
    }
    else
    {
        /* If the buffer is full, convert the 4 sextets of encoded data into
         * three sequential octets of decoded data starting from the most
         * significant bits and ending at the least significant bits. */
        if( numDataInBuffer == MAX_NUM_BASE64_DATA )
        {
            pDest[ outputLen ] = ( uint8_t ) ( ( base64IndexBuffer >> SIZE_OF_TWO_OCTETS ) & 0xFFU );
            pDest[ outputLen + 1U ] = ( uint8_t ) ( ( base64IndexBuffer >> SIZE_OF_ONE_OCTET ) & 0xFFU );
            pDest[ outputLen + 2U ] = ( uint8_t ) ( base64IndexBuffer & 0xFFU );
            outputLen += 3U;
        }

        if( numDataInBuffer == 3U )
        {
            /* When there are only three sextets of data remaining at the end of the encoded data,
             * it is assumed that these three sextets should be decoded into two octets of data. In
             * this case, the two least significant bits are ignored and the following sixteen
             * least significant bits are converted into two octets of data. */
            if( ( base64IndexBuffer & 0x3U ) != 0U )
            {
                returnVal = Base64NonZeroPadding;
            }

            if( returnVal == Base64Success )
            {
                base64IndexBuffer = base64IndexBuffer >> SIZE_OF_PADDING_WITH_THREE_SEXTETS;
                pDest[ outputLen ] = ( uint8_t ) ( ( base64IndexBuffer >> SIZE_OF_ONE_OCTET ) & 0xFFU );
                pDest[ outputLen + 1U ] = ( uint8_t ) ( base64IndexBuffer & 0xFFU );
                outputLen += 2U;
            }
        }

        if( numDataInBuffer == 2U )
        {
            /* When there are only two sextets of data remaining at the end of the encoded data, it
             * is assumed that these two sextets should be decoded into one octet of data. In this
             * case, the four least significant bits are ignored and the following eight least
             * significant bits are converted into one octet of data. */
            if( ( base64IndexBuffer & 0xFU ) != 0U )
            {
                returnVal = Base64NonZeroPadding;
            }

            if( returnVal == Base64Success )
            {
                base64IndexBuffer = base64IndexBuffer >> SIZE_OF_PADDING_WITH_TWO_SEXTETS;
                pDest[ outputLen ] = ( uint8_t ) ( base64IndexBuffer & 0xFFU );
                outputLen += 1U;
            }
        }
    }

    *pNumDataInBuffer = 0;
    *pOutputLen = outputLen;
    *pBase64IndexBuffer = 0;
    return returnVal;
}

/**
 * @brief Decode Base64 encoded data.
 *
 * @param[out] pDest Pointer to a buffer for storing the decoded result.
 * @param[in]  destLen Length of the pDest buffer.
 * @param[out] pResultLen Pointer to the length of the decoded result.
 * @param[in]  pEncodedData Pointer to a buffer containing the Base64 encoded
 *             data that is intended to be decoded.
 * @param[in]  encodedLen Length of the pEncodedData buffer.
 *
 * @return     One of the following:
 *             - #Base64Success if the Base64 encoded data was valid
 *               and successfully decoded.
 *             - An error code defined in ota_base64_private.h if the
 *               encoded data or input parameters are invalid.
 */
Base64Status_t base64Decode( uint8_t * pDest,
                             const size_t destLen,
                             size_t * pResultLen,
                             const uint8_t * pEncodedData,
                             const size_t encodedLen )
{
    uint32_t base64IndexBuffer = 0;
    uint32_t numDataInBuffer = 0;
    const uint8_t * pCurrBase64Symbol = pEncodedData;
    size_t outputLen = 0;
    int64_t numPadding = 0;
    int64_t numWhitespace = 0;
    Base64Status_t returnVal = Base64Success;

    if( ( pEncodedData == NULL ) || ( pDest == NULL ) || ( pResultLen == NULL ) )
    {
        returnVal = Base64NullPointerInput;
    }

    if( encodedLen < MIN_VALID_ENCODED_DATA_SIZE )
    {
        returnVal = Base64InvalidInputSize;
    }

    /* This loop will decode the first (encodedLen - (encodedLen % 4)) amount of data. */
    while( ( returnVal == Base64Success ) &&
           ( pCurrBase64Symbol < ( pEncodedData + encodedLen ) ) )
    {
        uint8_t base64Index = 0;
        /* Read in the next Ascii character that represents the current Base64 symbol. */
        uint8_t base64AsciiSymbol = *pCurrBase64Symbol++;
        /* Get the Base64 index that represents the Base64 symbol. */
        base64Index = pBase64SymbolToIndexMap[ base64AsciiSymbol ];

        /* Validate the input and update counters for padding and whitespace. */
        returnVal = preprocessBase64Index( base64Index,
                                           &numPadding,
                                           &numWhitespace );

        if( returnVal != Base64Success )
        {
            break;
        }

        /* Add the current Base64 index to a buffer. */
        updateBase64DecodingBuffer( base64Index,
                                    &base64IndexBuffer,
                                    &numDataInBuffer );

        /* Decode the buffer when it's full and store the result. */
        if( numDataInBuffer == MAX_NUM_BASE64_DATA )
        {
            returnVal = decodeBase64IndexBuffer( &base64IndexBuffer,
                                                 &numDataInBuffer,
                                                 pDest,
                                                 destLen,
                                                 &outputLen );
        }
    }

    if( returnVal == Base64Success )
    {
        /* This scenario is only possible when the number of encoded symbols ( excluding newlines
         * and padding ) being decoded mod four is equal to one. There is no valid scenario where
         * data can be encoded to create a result of this size. Therefore if this size is
         * encountered, it's assumed that the incoming Base64 data is not encoded correctly. */
        if( numDataInBuffer == 1U )
        {
            returnVal = Base64InvalidInputSize;
        }
    }

    if( returnVal == Base64Success )
    {
        /* Handle the scenarios where there is padding at the end of the encoded data.
         *
         * Note: This implementation assumes that non-zero padding bits are an error. This prevents
         * having multiple non-matching encoded data strings map to identical decoded strings. */
        if( ( numDataInBuffer == 2U ) || ( numDataInBuffer == 3U ) )
        {
            returnVal = decodeBase64IndexBuffer( &base64IndexBuffer,
                                                 &numDataInBuffer,
                                                 pDest,
                                                 destLen,
                                                 &outputLen );
        }
    }

    if( returnVal == Base64Success )
    {
        *pResultLen = outputLen;
    }

    return returnVal;
}

/*-----------------------------------------------------------*/
