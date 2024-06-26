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
 * @file ota_base64_utest.c
 * @brief Unit tests for functions in ota_base64.c
 */

#include <string.h>
#include "unity.h"

/* For accessing OTA private functions and error codes. */
#include "ota_base64_private.h"

/* Testing Constants. */

/* Buffer size that is large enough to hold the result of decoding any test string. */
#define BASE64_DEFAULT_TEST_DECODING_BUFFER_SIZE                      20

#define BASE64_VALID_DATA_TWO_PADDING_ENCODED                         "Rk9PQg=="
#define BASE64_VALID_DATA_TWO_PADDING_ENCODED_LEN                     ( sizeof( BASE64_VALID_DATA_TWO_PADDING_ENCODED ) - 1U )
#define BASE64_VALID_DATA_TWO_PADDING_DECODED                         "FOOB"
#define BASE64_VALID_DATA_TWO_PADDING_DECODED_LEN                     ( sizeof( BASE64_VALID_DATA_TWO_PADDING_DECODED ) - 1U )

#define BASE64_VALID_DATA_ONE_PADDING_ENCODED                         "Rk9PQkE="
#define BASE64_VALID_DATA_ONE_PADDING_ENCODED_LEN                     ( sizeof( BASE64_VALID_DATA_ONE_PADDING_ENCODED ) - 1U )
#define BASE64_VALID_DATA_ONE_PADDING_DECODED                         "FOOBA"
#define BASE64_VALID_DATA_ONE_PADDING_DECODED_LEN                     ( sizeof( BASE64_VALID_DATA_ONE_PADDING_DECODED ) - 1U )

#define BASE64_VALID_DATA_ZERO_PADDING_ENCODED                        "Rk9PQkFS"
#define BASE64_VALID_DATA_ZERO_PADDING_ENCODED_LEN                    ( sizeof( BASE64_VALID_DATA_ZERO_PADDING_ENCODED ) - 1U )
#define BASE64_VALID_DATA_ZERO_PADDING_DECODED                        "FOOBAR"
#define BASE64_VALID_DATA_ZERO_PADDING_DECODED_LEN                    ( sizeof( BASE64_VALID_DATA_ZERO_PADDING_DECODED ) - 1U )

#define BASE64_VALID_DATA_TWO_PADDING_REMOVED_ENCODED                 "Rk9PQg"
#define BASE64_VALID_DATA_TWO_PADDING_REMOVED_ENCODED_LEN             ( sizeof( BASE64_VALID_DATA_TWO_PADDING_REMOVED_ENCODED ) - 1U )
#define BASE64_VALID_DATA_TWO_PADDING_REMOVED_DECODED                 "FOOB"
#define BASE64_VALID_DATA_TWO_PADDING_REMOVED_DECODED_LEN             ( sizeof( BASE64_VALID_DATA_TWO_PADDING_REMOVED_DECODED ) - 1U )

#define BASE64_VALID_DATA_ONE_PADDING_REMOVED_ENCODED                 "Rk9PQkE"
#define BASE64_VALID_DATA_ONE_PADDING_REMOVED_ENCODED_LEN             ( sizeof( BASE64_VALID_DATA_ONE_PADDING_REMOVED_ENCODED ) - 1U )
#define BASE64_VALID_DATA_ONE_PADDING_REMOVED_DECODED                 "FOOBA"
#define BASE64_VALID_DATA_ONE_PADDING_REMOVED_DECODED_LEN             ( sizeof( BASE64_VALID_DATA_ONE_PADDING_REMOVED_DECODED ) - 1U )

#define BASE64_VALID_DATA_LF_ENCODED                                  "\nZm\n9v\n"
#define BASE64_VALID_DATA_LF_ENCODED_LEN                              ( sizeof( BASE64_VALID_DATA_LF_ENCODED ) - 1U )
#define BASE64_VALID_DATA_LF_DECODED                                  "foo"
#define BASE64_VALID_DATA_LF_DECODED_LEN                              ( sizeof( BASE64_VALID_DATA_LF_DECODED ) - 1U )

#define BASE64_VALID_DATA_CRLF_ENCODED                                "\r\nRk9P\r\nQkE=\r\n"
#define BASE64_VALID_DATA_CRLF_ENCODED_LEN                            ( sizeof( BASE64_VALID_DATA_CRLF_ENCODED ) - 1U )
#define BASE64_VALID_DATA_CRLF_DECODED                                "FOOBA"
#define BASE64_VALID_DATA_CRLF_DECODED_LEN                            ( sizeof( BASE64_VALID_DATA_CRLF_DECODED ) - 1U )

#define BASE64_VALID_DATA_WHITESPACE_ENCODED                          "Rk9PQkFS "
#define BASE64_VALID_DATA_WHITESPACE_ENCODED_LEN                      ( sizeof( BASE64_VALID_DATA_WHITESPACE_ENCODED ) - 1U )
#define BASE64_VALID_DATA_WHITESPACE_DECODED                          "FOOBAR"
#define BASE64_VALID_DATA_WHITESPACE_DECODED_LEN                      ( sizeof( BASE64_VALID_DATA_WHITESPACE_DECODED ) - 1U )

#define BASE64_VALID_DATA_PADDING_WHITESPACE_ENCODED                  "Rk9PQkE= "
#define BASE64_VALID_DATA_PADDING_WHITESPACE_ENCODED_LEN              ( sizeof( BASE64_VALID_DATA_PADDING_WHITESPACE_ENCODED ) - 1U )
#define BASE64_VALID_DATA_PADDING_WHITESPACE_DECODED                  "FOOBA"
#define BASE64_VALID_DATA_PADDING_WHITESPACE_DECODED_LEN              ( sizeof( BASE64_VALID_DATA_PADDING_WHITESPACE_DECODED ) - 1U )

/* This is arbitrary valid encoded/decoded data. This is intended to be used in a test where any
 * valid Base64 encoded string would suffice. */
#define BASE64_VALID_DATA_ENCODED                                     "Rk9PQkFSQkFa"
#define BASE64_VALID_DATA_ENCODED_LEN                                 ( sizeof( BASE64_VALID_DATA_ENCODED ) - 1U )
#define BASE64_VALID_DATA_DECODED                                     "FOOBARBAZ"
#define BASE64_VALID_DATA_DECODED_LEN                                 ( sizeof( BASE64_VALID_DATA_DECODED ) - 1U )

/* Created by adding one padding character to the valid encoded data string "Zg==". */
#define BASE64_INVALID_DATA_ONE_EXCESS_PADDING_ENCODED                "Zg==="
#define BASE64_INVALID_DATA_ONE_EXCESS_PADDING_ENCODED_LEN            ( sizeof( BASE64_INVALID_DATA_ONE_EXCESS_PADDING_ENCODED ) - 1U )

/* Created by adding two padding characters to the valid encoded data string "Rk9PQkE=". */
#define BASE64_INVALID_DATA_TWO_EXCESS_PADDING_ENCODED                "Rk9PQkE==="
#define BASE64_INVALID_DATA_TWO_EXCESS_PADDING_ENCODED_LEN            ( sizeof( BASE64_INVALID_DATA_TWO_EXCESS_PADDING_ENCODED ) - 1U )

/* Created by adding three padding characters to the valid encoded data string "Rk9PQkFS". */
#define BASE64_INVALID_DATA_THREE_EXCESS_PADDING_ENCODED              "Rk9PQkFS==="
#define BASE64_INVALID_DATA_THREE_EXCESS_PADDING_ENCODED_LEN          ( sizeof( BASE64_INVALID_DATA_THREE_EXCESS_PADDING_ENCODED ) - 1U )

/* This string was made by taking the valid Base64 encoded data "TWE=" and modifying the 'E' symbol.
 * The Base64 symbol 'E' has the Base64 index of four, which is represented by the sextet 0b000100.
 * In this context, the two least significant bits of the sextet are considered to be padding bits.
 * This sextet was modified by setting these padding bits to one, which results in the sextet
 * 0b000111. 0b000111 is seven, which is the Base64 index of the Base64 symbol 'G'.*/
#define BASE64_INVALID_DATA_TWO_NON_ZERO_PADDING_BITS_ENCODED         "TWG="
#define BASE64_INVALID_DATA_TWO_NON_ZERO_PADDING_BITS_ENCODED_LEN     ( sizeof( BASE64_INVALID_DATA_TWO_NON_ZERO_PADDING_BITS_ENCODED ) - 1U )

/* This string was made by taking the valid Base64 encoded data "TQ==" and modifying the 'Q' symbol.
 * The Base64 symbol 'Q' has the Base64 index of sixteen, which is represented by the sextet 0b010000.
 * In this context, the four least significant bits of the sextet are considered to be padding bits.
 * This sextet was modified by setting these padding bits to one, which results in the sextet
 * 0b011111. 0b011111 is thirty-one, which is the Base64 index of the Base64 symbol 'f'.*/
#define BASE64_INVALID_DATA_FOUR_NON_ZERO_PADDING_BITS_ENCODED        "Tf=="
#define BASE64_INVALID_DATA_FOUR_NON_ZERO_PADDING_BITS_ENCODED_LEN    ( sizeof( BASE64_INVALID_DATA_FOUR_NON_ZERO_PADDING_BITS_ENCODED ) - 1U )

#define BASE64_INVALID_DATA_WHITESPACE_AT_FRONT_ENCODED               " Rk9PQkFS"
#define BASE64_INVALID_DATA_WHITESPACE_AT_FRONT_ENCODED_LEN           ( sizeof( BASE64_INVALID_DATA_WHITESPACE_AT_FRONT_ENCODED ) - 1U )

#define BASE64_INVALID_DATA_WHITESPACE_AT_MIDDLE_ENCODED              "Rk9P QkFS"
#define BASE64_INVALID_DATA_WHITESPACE_AT_MIDDLE_ENCODED_LEN          ( sizeof( BASE64_INVALID_DATA_WHITESPACE_AT_MIDDLE_ENCODED ) - 1U )

#define BASE64_INVALID_DATA_WHITESPACE_BEFORE_PADDING_ENCODED         "Rk9PQkE ="
#define BASE64_INVALID_DATA_WHITESPACE_BEFORE_PADDING_ENCODED_LEN     ( sizeof( BASE64_INVALID_DATA_WHITESPACE_BEFORE_PADDING_ENCODED ) - 1U )

#define BASE64_INVALID_DATA_IMPOSSIBLY_SMALL_ENCODED                  "R"
#define BASE64_INVALID_DATA_IMPOSSIBLY_SMALL_ENCODED_LEN              ( sizeof( BASE64_INVALID_DATA_IMPOSSIBLY_SMALL_ENCODED ) - 1U )

/* This string represents the scenario where encoded data, excluding the padding, mod four is equal
 * to one. This is significant because there is no input data that can be encoded to create an
 * encoded data string of this length. */
#define BASE64_INVALID_DATA_IMPOSSIBLE_LENGTH_ENCODED                 "Rk9PC=="
#define BASE64_INVALID_DATA_IMPOSSIBLE_LENGTH_ENCODED_LEN             ( sizeof( BASE64_INVALID_DATA_IMPOSSIBLE_LENGTH_ENCODED ) - 1U )

#define BASE64_INVALID_DATA_PADDING_AT_FRONT_ENCODED                  "=Rk9PQkFS"
#define BASE64_INVALID_DATA_PADDING_AT_FRONT_ENCODED_LEN              ( sizeof( BASE64_INVALID_DATA_PADDING_AT_FRONT_ENCODED ) - 1U )

#define BASE64_INVALID_DATA_PADDING_AT_MIDDLE_ENCODED                 "Rk9P=QkFS"
#define BASE64_INVALID_DATA_PADDING_AT_MIDDLE_ENCODED_LEN             ( sizeof( BASE64_INVALID_DATA_PADDING_AT_MIDDLE_ENCODED ) - 1U )

/* ============================   UNITY FIXTURES ============================ */

void setUp( void )
{
}

void tearDown( void )
{
}

/* ========================================================================== */

/**
 * @brief Test that base64Decode is able to decode valid data with two padding
 *        symbols correctly.
 */
void test_OTA_base64Decode_ValidTwoPaddingSymbols( void )
{
    uint8_t pDecodedResultBuffer[ BASE64_DEFAULT_TEST_DECODING_BUFFER_SIZE ] = { 0 };
    size_t resultLen = 0;
    int result = 0;

    result = base64Decode( pDecodedResultBuffer,
                           BASE64_DEFAULT_TEST_DECODING_BUFFER_SIZE,
                           &resultLen,
                           ( const uint8_t * ) BASE64_VALID_DATA_TWO_PADDING_ENCODED,
                           BASE64_VALID_DATA_TWO_PADDING_ENCODED_LEN );

    TEST_ASSERT_EQUAL_INT( Base64Success, result );
    TEST_ASSERT_EQUAL_INT( BASE64_VALID_DATA_TWO_PADDING_DECODED_LEN, resultLen );
    TEST_ASSERT_EQUAL_STRING_LEN( BASE64_VALID_DATA_TWO_PADDING_DECODED, pDecodedResultBuffer, resultLen );
}

/**
 * @brief Test that base64Decode is able to decode valid data with one padding
 *        symbols correctly.
 */
void test_OTA_base64Decode_ValidOnePaddingSymbol( void )
{
    uint8_t pDecodedResultBuffer[ BASE64_DEFAULT_TEST_DECODING_BUFFER_SIZE ] = { 0 };
    size_t resultLen = 0;
    int result = 0;

    result = base64Decode( pDecodedResultBuffer,
                           BASE64_DEFAULT_TEST_DECODING_BUFFER_SIZE,
                           &resultLen,
                           ( const uint8_t * ) BASE64_VALID_DATA_ONE_PADDING_ENCODED,
                           BASE64_VALID_DATA_ONE_PADDING_ENCODED_LEN );

    TEST_ASSERT_EQUAL_INT( Base64Success, result );
    TEST_ASSERT_EQUAL_INT( BASE64_VALID_DATA_ONE_PADDING_DECODED_LEN, resultLen );
    TEST_ASSERT_EQUAL_STRING_LEN( BASE64_VALID_DATA_ONE_PADDING_DECODED, pDecodedResultBuffer, resultLen );
}

/**
 * @brief Test that base64Decode is able to decode valid data with no padding
 *        symbols correctly.
 */
void test_OTA_base64Decode_ValidNoPaddingSymbols( void )
{
    uint8_t pDecodedResultBuffer[ BASE64_DEFAULT_TEST_DECODING_BUFFER_SIZE ] = { 0 };
    size_t resultLen = 0;
    int result = 0;

    result = base64Decode( pDecodedResultBuffer,
                           BASE64_DEFAULT_TEST_DECODING_BUFFER_SIZE,
                           &resultLen,
                           ( const uint8_t * ) BASE64_VALID_DATA_ZERO_PADDING_ENCODED,
                           BASE64_VALID_DATA_ZERO_PADDING_ENCODED_LEN );

    TEST_ASSERT_EQUAL_INT( Base64Success, result );
    TEST_ASSERT_EQUAL_INT( BASE64_VALID_DATA_ZERO_PADDING_DECODED_LEN, resultLen );
    TEST_ASSERT_EQUAL_STRING_LEN( BASE64_VALID_DATA_ZERO_PADDING_DECODED, pDecodedResultBuffer, resultLen );
}

/**
 * @brief Test that base64Decode is able to decode valid data when the optional
 *        padding symbols are removed.
 */
void test_OTA_base64Decode_ValidNoOptionalPadding( void )
{
    uint8_t pDecodedResultBuffer[ BASE64_DEFAULT_TEST_DECODING_BUFFER_SIZE ] = { 0 };
    size_t resultLen = 0;
    int result = 0;

    /* Test having no padding symbols when there could be two valid padding symbols. */
    result = base64Decode( pDecodedResultBuffer,
                           BASE64_DEFAULT_TEST_DECODING_BUFFER_SIZE,
                           &resultLen,
                           ( const uint8_t * ) BASE64_VALID_DATA_TWO_PADDING_REMOVED_ENCODED,
                           BASE64_VALID_DATA_TWO_PADDING_REMOVED_ENCODED_LEN );

    TEST_ASSERT_EQUAL_INT( Base64Success, result );
    TEST_ASSERT_EQUAL_INT( BASE64_VALID_DATA_TWO_PADDING_REMOVED_DECODED_LEN, resultLen );
    TEST_ASSERT_EQUAL_STRING_LEN( BASE64_VALID_DATA_TWO_PADDING_REMOVED_DECODED, pDecodedResultBuffer, resultLen );

    /* Test having no padding symbols when there could be one valid padding symbol. */
    resultLen = 0;
    memset( pDecodedResultBuffer, '\0', sizeof( pDecodedResultBuffer ) );
    result = base64Decode( pDecodedResultBuffer,
                           BASE64_DEFAULT_TEST_DECODING_BUFFER_SIZE,
                           &resultLen,
                           ( const uint8_t * ) BASE64_VALID_DATA_ONE_PADDING_REMOVED_ENCODED,
                           BASE64_VALID_DATA_ONE_PADDING_REMOVED_ENCODED_LEN );

    TEST_ASSERT_EQUAL_INT( Base64Success, result );
    TEST_ASSERT_EQUAL_INT( BASE64_VALID_DATA_ONE_PADDING_REMOVED_DECODED_LEN, resultLen );
    TEST_ASSERT_EQUAL_STRING_LEN( BASE64_VALID_DATA_ONE_PADDING_REMOVED_DECODED, pDecodedResultBuffer, resultLen );
}

/**
 * @brief Test that base64Decode is able to decode valid data that contains a
 *        line feed symbol at the start, middle, and end.
 */
void test_OTA_base64Decode_ValidDataContainsLF( void )
{
    uint8_t pDecodedResultBuffer[ BASE64_DEFAULT_TEST_DECODING_BUFFER_SIZE ] = { 0 };
    size_t resultLen = 0;
    int result = 0;

    result = base64Decode( pDecodedResultBuffer,
                           BASE64_DEFAULT_TEST_DECODING_BUFFER_SIZE,
                           &resultLen,
                           ( const uint8_t * ) BASE64_VALID_DATA_LF_ENCODED,
                           BASE64_VALID_DATA_LF_ENCODED_LEN );

    TEST_ASSERT_EQUAL_INT( Base64Success, result );
    TEST_ASSERT_EQUAL_INT( BASE64_VALID_DATA_LF_DECODED_LEN, resultLen );
    TEST_ASSERT_EQUAL_STRING_LEN( BASE64_VALID_DATA_LF_DECODED, pDecodedResultBuffer, resultLen );
}

/**
 * @brief Test that base64Decode is able to decode valid data that contains a
 *        carriage return and a line feed at the beginning, middle, and end.
 */
void test_OTA_base64Decode_ValidDataContainsCRLF( void )
{
    uint8_t pDecodedResultBuffer[ BASE64_DEFAULT_TEST_DECODING_BUFFER_SIZE ] = { 0 };
    size_t resultLen = 0;
    int result = 0;

    result = base64Decode( pDecodedResultBuffer,
                           BASE64_DEFAULT_TEST_DECODING_BUFFER_SIZE,
                           &resultLen,
                           ( const uint8_t * ) BASE64_VALID_DATA_CRLF_ENCODED,
                           BASE64_VALID_DATA_CRLF_ENCODED_LEN );

    TEST_ASSERT_EQUAL_INT( Base64Success, result );
    TEST_ASSERT_EQUAL_INT( BASE64_VALID_DATA_CRLF_DECODED_LEN, resultLen );
    TEST_ASSERT_EQUAL_STRING_LEN( BASE64_VALID_DATA_CRLF_DECODED, pDecodedResultBuffer, resultLen );
}

/**
 * @brief Test that base64Decode is able to decode and store valid data when
 *        the output buffer is exactly the size that it needs to be contain
 *        the decoded data.
 */
void test_OTA_base64Decode_ValidDecodeBufferExactSize( void )
{
    uint8_t pDecodedResultBuffer[ BASE64_VALID_DATA_DECODED_LEN ] = { 0 };
    size_t resultLen = 0;
    int result = 0;

    result = base64Decode( pDecodedResultBuffer,
                           BASE64_VALID_DATA_DECODED_LEN,
                           &resultLen,
                           ( const uint8_t * ) BASE64_VALID_DATA_ENCODED,
                           BASE64_VALID_DATA_ENCODED_LEN );

    TEST_ASSERT_EQUAL_INT( Base64Success, result );
    TEST_ASSERT_EQUAL_INT( BASE64_VALID_DATA_DECODED_LEN, resultLen );
    TEST_ASSERT_EQUAL_STRING_LEN( BASE64_VALID_DATA_DECODED, pDecodedResultBuffer, resultLen );
}

/**
 * @brief Test that base64Decode is able to decode valid data when there are
 *        whitespace characters at the end of it.
 */
void test_OTA_base64Decode_ValidWhitespace( void )
{
    uint8_t pDecodedResultBuffer[ BASE64_DEFAULT_TEST_DECODING_BUFFER_SIZE ] = { 0 };
    size_t resultLen = 0;
    int result = 0;

    /* Test for having a whitespace character at the start of a valid Base64
     * encoded data string without padding. */
    result = base64Decode( pDecodedResultBuffer,
                           BASE64_DEFAULT_TEST_DECODING_BUFFER_SIZE,
                           &resultLen,
                           ( const uint8_t * ) BASE64_VALID_DATA_WHITESPACE_ENCODED,
                           BASE64_VALID_DATA_WHITESPACE_ENCODED_LEN );

    TEST_ASSERT_EQUAL_INT( Base64Success, result );
    TEST_ASSERT_EQUAL_INT( BASE64_VALID_DATA_WHITESPACE_DECODED_LEN, resultLen );
    TEST_ASSERT_EQUAL_STRING_LEN( BASE64_VALID_DATA_WHITESPACE_DECODED, pDecodedResultBuffer, resultLen );

    /* Test for having a whitespace character at the end of a valid Base64
     * encoded data string with padding. */
    resultLen = 0;
    memset( pDecodedResultBuffer, '\0', sizeof( pDecodedResultBuffer ) );
    result = base64Decode( pDecodedResultBuffer,
                           BASE64_DEFAULT_TEST_DECODING_BUFFER_SIZE,
                           &resultLen,
                           ( const uint8_t * ) BASE64_VALID_DATA_PADDING_WHITESPACE_ENCODED,
                           BASE64_VALID_DATA_PADDING_WHITESPACE_ENCODED_LEN );

    TEST_ASSERT_EQUAL_INT( Base64Success, result );
    TEST_ASSERT_EQUAL_INT( BASE64_VALID_DATA_PADDING_WHITESPACE_DECODED_LEN, resultLen );
    TEST_ASSERT_EQUAL_STRING_LEN( BASE64_VALID_DATA_PADDING_WHITESPACE_DECODED, pDecodedResultBuffer, resultLen );
}

/**
 * @brief Test that base64Decode returns Base64NullPointerInput when a null
 *        pointer is passed into the function.
 */
void test_OTA_base64Decode_InvalidNullInputs( void )
{
    uint8_t pDecodedResultBuffer[ BASE64_DEFAULT_TEST_DECODING_BUFFER_SIZE ] = { 0 };
    int result = 0;
    size_t resultLen = 0;

    /* Test for having a null pointer passed in for pDest while other
     * parameters are valid. */
    result = base64Decode( NULL,
                           BASE64_DEFAULT_TEST_DECODING_BUFFER_SIZE,
                           &resultLen,
                           ( const uint8_t * ) BASE64_VALID_DATA_ENCODED,
                           BASE64_VALID_DATA_ENCODED_LEN );
    TEST_ASSERT_EQUAL_INT( Base64NullPointerInput, result );

    /* Test for having a null pointer passed in for pResultLen while other
     * parameters are valid. */
    resultLen = 0;
    memset( pDecodedResultBuffer, '\0', sizeof( pDecodedResultBuffer ) );
    result = base64Decode( pDecodedResultBuffer,
                           BASE64_DEFAULT_TEST_DECODING_BUFFER_SIZE,
                           NULL,
                           ( const uint8_t * ) BASE64_VALID_DATA_ENCODED,
                           BASE64_VALID_DATA_ENCODED_LEN );
    TEST_ASSERT_EQUAL_INT( Base64NullPointerInput, result );

    /* Test for having a null pointer passed in for pEncodedData while other
     * parameters are valid. */
    resultLen = 0;
    memset( pDecodedResultBuffer, '\0', sizeof( pDecodedResultBuffer ) );
    result = base64Decode( pDecodedResultBuffer,
                           BASE64_DEFAULT_TEST_DECODING_BUFFER_SIZE,
                           &resultLen,
                           NULL,
                           BASE64_VALID_DATA_ENCODED_LEN );
    TEST_ASSERT_EQUAL_INT( Base64NullPointerInput, result );
}

/**
 * @brief Test that base64Decode returns Base64InvalidPaddingSymbol
 *        when there are three padding symbols in the encoded data.
 */
void test_OTA_base64Decode_InvalidThreePaddingSymbols( void )
{
    uint8_t pDecodedResultBuffer[ BASE64_DEFAULT_TEST_DECODING_BUFFER_SIZE ] = { 0 };
    int result = 0;
    size_t resultLen = 0;

    /* Test for three padding characters when there should be only two or zero. */
    result = base64Decode( pDecodedResultBuffer,
                           BASE64_DEFAULT_TEST_DECODING_BUFFER_SIZE,
                           &resultLen,
                           ( const uint8_t * ) BASE64_INVALID_DATA_ONE_EXCESS_PADDING_ENCODED,
                           BASE64_INVALID_DATA_ONE_EXCESS_PADDING_ENCODED_LEN );
    TEST_ASSERT_EQUAL_INT( Base64InvalidPaddingSymbol, result );

    /* Test for three padding characters when there should be only one or zero. */
    resultLen = 0;
    memset( pDecodedResultBuffer, '\0', sizeof( pDecodedResultBuffer ) );
    result = base64Decode( pDecodedResultBuffer,
                           BASE64_DEFAULT_TEST_DECODING_BUFFER_SIZE,
                           &resultLen,
                           ( const uint8_t * ) BASE64_INVALID_DATA_TWO_EXCESS_PADDING_ENCODED,
                           BASE64_INVALID_DATA_TWO_EXCESS_PADDING_ENCODED_LEN );
    TEST_ASSERT_EQUAL_INT( Base64InvalidPaddingSymbol, result );

    /* Test for three padding characters when there should be zero. */
    resultLen = 0;
    memset( pDecodedResultBuffer, '\0', sizeof( pDecodedResultBuffer ) );
    result = base64Decode( pDecodedResultBuffer,
                           BASE64_DEFAULT_TEST_DECODING_BUFFER_SIZE,
                           &resultLen,
                           ( const uint8_t * ) BASE64_INVALID_DATA_THREE_EXCESS_PADDING_ENCODED,
                           BASE64_INVALID_DATA_THREE_EXCESS_PADDING_ENCODED_LEN );
    TEST_ASSERT_EQUAL_INT( Base64InvalidPaddingSymbol, result );
}

/**
 * @brief Test that base64Decode returns Base64InvalidSymbol when
 *        there is a symbol that is not a valid Base64 symbol. The valid Base64
 *        symbols are assumed to be the Base64 digits, line feeds, carriage
 *        returns, spaces, and the padding symbol '='.
 */
void test_OTA_base64Decode_InvalidNonBase64Symbols( void )
{
    uint8_t pModifiedEncodedData[ BASE64_VALID_DATA_ENCODED_LEN ] = BASE64_VALID_DATA_ENCODED;
    uint8_t pDecodedResultBuffer[ BASE64_DEFAULT_TEST_DECODING_BUFFER_SIZE ] = { 0 };
    int result = 0, i = 0, numInvalidSymbols = 0;
    size_t resultLen = 0;

    /* Table of numbers representing all Ascii symbols other than the valid
     * Base64 symbols. Valid symbols are: "ABCDEFGHIJKLMNOPQRSTUVWXYZ",
     * "abcdefghijklmnopqrstuvwxyz", "0123456789", "+", "/", space, LF, CR, and
     * '='. */
    char invalidAsciiSymbols[] =
    {
        0,   1,   2,   3,   4,   5,   6,   7,   8,   9,
        11,  12,  14,  15,  16,  17,  18,  19,  20,  21,
        22,  23,  24,  25,  26,  27,  28,  29,  30,  31,
        33,  34,  35,  36,  37,  38,  39,  40,  41,  42,
        44,  45,  46,  58,  59,  60,  62,  63,  91,  92,
        93,  94,  95,  96,  123, 124, 125, 126, 127, 128,
        129, 130, 131, 132, 133, 134, 135, 136, 137, 138,
        139, 140, 141, 142, 143, 144, 145, 146, 147, 148,
        149, 150, 151, 152, 153, 154, 155, 156, 157, 158,
        159, 160, 161, 162, 163, 164, 165, 166, 167, 168,
        169, 170, 171, 172, 173, 174, 175, 176, 177, 178,
        179, 180, 181, 182, 183, 184, 185, 186, 187, 188,
        189, 190, 191, 192, 193, 194, 195, 196, 197, 198,
        199, 200, 201, 202, 203, 204, 205, 206, 207, 208,
        209, 210, 211, 212, 213, 214, 215, 216, 217, 218,
        219, 220, 221, 222, 223, 224, 225, 226, 227, 228,
        229, 230, 231, 232, 233, 234, 235, 236, 237, 238,
        239, 240, 241, 242, 243, 244, 245, 246, 247, 248,
        249, 250, 251, 252, 253, 254, 255
    };

    numInvalidSymbols = sizeof( invalidAsciiSymbols ) / sizeof( invalidAsciiSymbols[ 0 ] );

    /* Test inserting every non-Base64 symbol into the encoded data one at a time. */
    for( i = 0; i < numInvalidSymbols; ++i )
    {
        pModifiedEncodedData[ 0 ] = invalidAsciiSymbols[ i ];
        resultLen = 0;
        result = base64Decode( pDecodedResultBuffer,
                               BASE64_DEFAULT_TEST_DECODING_BUFFER_SIZE,
                               &resultLen,
                               pModifiedEncodedData,
                               BASE64_VALID_DATA_ENCODED_LEN );
        TEST_ASSERT_EQUAL_INT( Base64InvalidSymbol, result );
    }
}

/**
 * @brief Test that base64Decode returns Base64NonZeroPadding when
 *        the encoded data contains padding bits and they are not set to zero.
 */
void test_OTA_base64Decode_InvalidNonZeroPaddingBits( void )
{
    uint8_t pDecodedResultBuffer[ BASE64_DEFAULT_TEST_DECODING_BUFFER_SIZE ] = { 0 };
    int result = 0;
    size_t resultLen = 0;

    /* Test the case where there are two padding bits and they have non-zero values. */
    result = base64Decode( pDecodedResultBuffer,
                           BASE64_DEFAULT_TEST_DECODING_BUFFER_SIZE,
                           &resultLen,
                           ( const uint8_t * ) BASE64_INVALID_DATA_TWO_NON_ZERO_PADDING_BITS_ENCODED,
                           BASE64_INVALID_DATA_TWO_NON_ZERO_PADDING_BITS_ENCODED_LEN );
    TEST_ASSERT_EQUAL_INT( Base64NonZeroPadding, result );

    /* Test the case where there are four padding bits and they have non-zero values. */
    resultLen = 0;
    memset( pDecodedResultBuffer, '\0', sizeof( pDecodedResultBuffer ) );
    result = base64Decode( pDecodedResultBuffer,
                           BASE64_DEFAULT_TEST_DECODING_BUFFER_SIZE,
                           &resultLen,
                           ( const uint8_t * ) BASE64_INVALID_DATA_FOUR_NON_ZERO_PADDING_BITS_ENCODED,
                           BASE64_INVALID_DATA_FOUR_NON_ZERO_PADDING_BITS_ENCODED_LEN );
    TEST_ASSERT_EQUAL_INT( Base64NonZeroPadding, result );
}

/**
 * @brief Test that base64Decode returns Base64InvalidSymbolOrdering
 *        when the encoded data contains spaces that are in places other than
 *        the end of the string.
 */
void test_OTA_base64Decode_InvalidWhitespace( void )
{
    uint8_t pDecodedResultBuffer[ BASE64_DEFAULT_TEST_DECODING_BUFFER_SIZE ] = { 0 };
    int result = 0;
    size_t resultLen = 0;

    /* Test for having a whitespace character at the start of an otherwise
     * valid Base64 encoded data string. */
    result = base64Decode( pDecodedResultBuffer,
                           BASE64_DEFAULT_TEST_DECODING_BUFFER_SIZE,
                           &resultLen,
                           ( const uint8_t * ) BASE64_INVALID_DATA_WHITESPACE_AT_FRONT_ENCODED,
                           BASE64_INVALID_DATA_WHITESPACE_AT_FRONT_ENCODED_LEN );
    TEST_ASSERT_EQUAL_INT( Base64InvalidSymbolOrdering, result );

    /* Test for having a whitespace character in the middle of an otherwise
     * valid Base64 encoded data string. */
    resultLen = 0;
    memset( pDecodedResultBuffer, '\0', sizeof( pDecodedResultBuffer ) );
    result = base64Decode( pDecodedResultBuffer,
                           BASE64_DEFAULT_TEST_DECODING_BUFFER_SIZE,
                           &resultLen,
                           ( const uint8_t * ) BASE64_INVALID_DATA_WHITESPACE_AT_MIDDLE_ENCODED,
                           BASE64_INVALID_DATA_WHITESPACE_AT_MIDDLE_ENCODED_LEN );
    TEST_ASSERT_EQUAL_INT( Base64InvalidSymbolOrdering, result );

    /* Test for having a whitespace character in between the valid Base64
     * encoded data and a valid padding character. */
    resultLen = 0;
    memset( pDecodedResultBuffer, '\0', sizeof( pDecodedResultBuffer ) );
    result = base64Decode( pDecodedResultBuffer,
                           BASE64_DEFAULT_TEST_DECODING_BUFFER_SIZE,
                           &resultLen,
                           ( const uint8_t * ) BASE64_INVALID_DATA_WHITESPACE_BEFORE_PADDING_ENCODED,
                           BASE64_INVALID_DATA_WHITESPACE_BEFORE_PADDING_ENCODED_LEN );
    TEST_ASSERT_EQUAL_INT( Base64InvalidSymbolOrdering, result );
}

/**
 * @brief Test that base64Decode returns Base64InvalidInputSize when
 *        the encoded data is impossibly small. The smallest amount of data
 *        that can be encoded is one byte. When one byte is encoded, it will
 *        always result in two bytes of data.
 */
void test_OTA_base64Decode_InvalidInputSize( void )
{
    uint8_t pDecodedResultBuffer[ BASE64_DEFAULT_TEST_DECODING_BUFFER_SIZE ] = { 0 };
    int result = 0;
    size_t resultLen = 0;

    /* Correctly encoded data will always be at least two Base64 symbols. */
    result = base64Decode( pDecodedResultBuffer,
                           BASE64_DEFAULT_TEST_DECODING_BUFFER_SIZE,
                           &resultLen,
                           ( const uint8_t * ) BASE64_INVALID_DATA_IMPOSSIBLY_SMALL_ENCODED,
                           BASE64_INVALID_DATA_IMPOSSIBLY_SMALL_ENCODED_LEN );
    TEST_ASSERT_EQUAL_INT( Base64InvalidInputSize, result );
}

/**
 * @brief Test that base64Decode returns Base64InvalidBufferSize
 *        when the buffer passed in for the pDest parameter is too small to
 *        contain the decoded result.
 */
void test_OTA_base64Decode_InvalidDecodeBufferSize( void )
{
    /* This buffer size is one less than what's required to store the result. */
    uint8_t pDecodedResultBuffer[ BASE64_VALID_DATA_DECODED_LEN - 1U ] = { 0 };
    int result = 0;
    size_t resultLen = 0;

    /* Test for having the buffer intended for storing the decoded result be
     * too small to contain the output. */
    result = base64Decode( pDecodedResultBuffer,
                           ( BASE64_VALID_DATA_DECODED_LEN - 1U ),
                           &resultLen,
                           ( const uint8_t * ) BASE64_VALID_DATA_ENCODED,
                           BASE64_VALID_DATA_ENCODED_LEN );
    TEST_ASSERT_EQUAL_INT( Base64InvalidBufferSize, result );
}

/**
 * @brief Test that base64Decode returns Base64InvalidInputSize when the
 *        encoded data to decode is a length that is not possible if the
 *        original encoded data was encoded correctly.
 */
void test_OTA_base64Decode_InvalidEncodedDataLength( void )
{
    uint8_t pDecodedResultBuffer[ BASE64_DEFAULT_TEST_DECODING_BUFFER_SIZE ] = { 0 };
    int result = 0;
    size_t resultLen = 0;

    /* Test for when the encoded data excluding padding mod four is equal to
     * one. There is no valid encoding scheme that can produce this, so it's
     * considered an error. */
    result = base64Decode( pDecodedResultBuffer,
                           BASE64_DEFAULT_TEST_DECODING_BUFFER_SIZE,
                           &resultLen,
                           ( const uint8_t * ) BASE64_INVALID_DATA_IMPOSSIBLE_LENGTH_ENCODED,
                           BASE64_INVALID_DATA_IMPOSSIBLE_LENGTH_ENCODED_LEN );
    TEST_ASSERT_EQUAL_INT( Base64InvalidInputSize, result );
}

/**
 * @brief Test that base64Decode returns Base64InvalidSymbolOrdering
 *        when the encoded data to decode has a padding symbol that is located
 *        somewhere other than at the end of the data.
 */
void test_OTA_base64Decode_InvalidPaddingPlacement( void )
{
    uint8_t pDecodedResultBuffer[ BASE64_DEFAULT_TEST_DECODING_BUFFER_SIZE ] = { 0 };
    int result = 0;
    size_t resultLen = 0;

    /* Test for when a Base64 padding symbol is at the start of otherwise valid data. */
    result = base64Decode( pDecodedResultBuffer,
                           BASE64_DEFAULT_TEST_DECODING_BUFFER_SIZE,
                           &resultLen,
                           ( const uint8_t * ) BASE64_INVALID_DATA_PADDING_AT_FRONT_ENCODED,
                           BASE64_INVALID_DATA_PADDING_AT_FRONT_ENCODED_LEN );
    TEST_ASSERT_EQUAL_INT( Base64InvalidSymbolOrdering, result );

    /* Test for when a Base64 padding symbol in the middle of otherwise valid data. */
    resultLen = 0;
    memset( pDecodedResultBuffer, '\0', sizeof( pDecodedResultBuffer ) );
    result = base64Decode( pDecodedResultBuffer,
                           BASE64_DEFAULT_TEST_DECODING_BUFFER_SIZE,
                           &resultLen,
                           ( const uint8_t * ) BASE64_INVALID_DATA_PADDING_AT_MIDDLE_ENCODED,
                           BASE64_INVALID_DATA_PADDING_AT_MIDDLE_ENCODED_LEN );
    TEST_ASSERT_EQUAL_INT( Base64InvalidSymbolOrdering, result );
}

/* ========================================================================== */
