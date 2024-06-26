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
 * @file ota_base64_private.h
 * @brief Function declarations and error codes for ota_base64.c.
 */

#ifndef OTA_BASE64_PRIVATE_H
#define OTA_BASE64_PRIVATE_H

/* *INDENT-OFF* */
#ifdef __cplusplus
    extern "C" {
#endif
/* *INDENT-ON* */

/* Standard includes. */
#include <stdint.h>
#include <stdlib.h>

/**
 * ota_enum_types
 * @brief The Base64 functionality return status.
 */
typedef enum Base64Status
{
    /**
     * @brief Base64 function success.
     */
    Base64Success,

    /**
     * @brief Invalid symbol in the encoded data.
     */
    Base64InvalidSymbol,

    /**
     * @brief A Base64 symbol is in an invalid location within the encoded data.
     */
    Base64InvalidSymbolOrdering,

    /**
     * @brief Length of the encoded data is impossible to have been created with
     *        valid Base64 encoding.
     */
    Base64InvalidInputSize,

    /**
     * @brief Input parameter for pointer is null.
     */
    Base64NullPointerInput,

    /**
     * @brief Provided buffer is too small.
     */
    Base64InvalidBufferSize,

    /**
     * @brief Padding bits inside of the encoded data are invalid because they are
     *        not zero.
     */
    Base64NonZeroPadding,

    /**
     * @brief Invalid number of padding symbols.
     */
    Base64InvalidPaddingSymbol
} Base64Status_t;

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
                             const size_t encodedLen );

/* *INDENT-OFF* */
#ifdef __cplusplus
    }
#endif
/* *INDENT-ON* */

#endif /* ifndef OTA_BASE64_PRIVATE_H */
