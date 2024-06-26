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
 * @file ota_appversion32.h
 * @brief Structure to represent the application build version.
 */

#ifndef IOT_APPVERSION32_H
#define IOT_APPVERSION32_H

/* *INDENT-OFF* */
#ifdef __cplusplus
    extern "C" {
#endif
/* *INDENT-ON* */

/* Standard includes. */
#include <stdint.h>

/**
 * @ingroup ota_struct_types
 * @brief Application version structure.
 *
 */
typedef struct
{
    /* MISRA Ref 19.2.1 [Unions] */
    /* More details at: https://github.com/aws/ota-for-aws-iot-embedded-sdk/blob/main/MISRA.md#rule-192 */
    /* coverity[misra_c_2012_rule_19_2_violation] */
    union
    {
        #if ( defined( __BYTE_ORDER__ ) && defined( __ORDER_LITTLE_ENDIAN__ ) && ( __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__ ) ) || ( __little_endian__ == 1 ) || WIN32 || ( __BYTE_ORDER == __LITTLE_ENDIAN )
            struct version
            {
                uint16_t build; /*!< @brief Build of the firmware (Z in firmware version Z.Y.X). */
                uint8_t minor;  /*!< @brief Minor version number of the firmware (Y in firmware version Z.Y.X). */

                uint8_t major;  /*!< @brief Major version number of the firmware (X in firmware version Z.Y.X). */
            } x;                /*!< @brief Version number of the firmware. */
        #elif ( defined( __BYTE_ORDER__ ) && defined( __ORDER_BIG_ENDIAN__ ) && __BYTE_ORDER__ == __ORDER_BIG_ENDIAN__ ) || ( __big_endian__ == 1 ) || ( __BYTE_ORDER == __BIG_ENDIAN )
            struct version
            {
                uint8_t major;  /*!< @brief Major version number of the firmware (X in firmware version X.Y.Z). */
                uint8_t minor;  /*!< @brief Minor version number of the firmware (Y in firmware version X.Y.Z). */

                uint16_t build; /*!< @brief Build of the firmware (Z in firmware version X.Y.Z). */
            } x;                /*!< @brief Version number of the firmware. */
        #else /* if ( defined( __BYTE_ORDER__ ) && defined( __ORDER_LITTLE_ENDIAN__ ) && __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__ ) || ( __little_endian__ == 1 ) || WIN32 || ( __BYTE_ORDER == __LITTLE_ENDIAN ) */
        #error "Unable to determine byte order!"
        #endif /* if ( defined( __BYTE_ORDER__ ) && defined( __ORDER_LITTLE_ENDIAN__ ) && __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__ ) || ( __little_endian__ == 1 ) || WIN32 || ( __BYTE_ORDER == __LITTLE_ENDIAN ) */
        uint32_t unsignedVersion32;
        int32_t signedVersion32;
    } u; /*!< @brief Version based on configuration in big endian or little endian. */
} AppVersion32_t;

extern const AppVersion32_t appFirmwareVersion; /*!< @brief Making the version number available globally through external linkage. */

/* *INDENT-OFF* */
#ifdef __cplusplus
    }
#endif
/* *INDENT-ON* */

#endif /* ifndef IOT_APPVERSION32_H */
