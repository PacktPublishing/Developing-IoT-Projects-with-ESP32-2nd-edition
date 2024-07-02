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
 * @file ota_config.h
 * @brief OTA user configurable settings.
 */

#ifndef OTA_CONFIG_H_
#define OTA_CONFIG_H_

/* Enable both MQTT and HTTP in unit tests. */
#define configENABLED_DATA_PROTOCOLS            ( OTA_DATA_OVER_MQTT | OTA_DATA_OVER_HTTP )

/* Call status update for every block that we received so that we can hit some internal routines. */
#define otaconfigOTA_UPDATE_STATUS_FREQUENCY    2

/* Lower request momentum so that retry fails faster. */
#define otaconfigMAX_NUM_REQUEST_MOMENTUM       3

/* Use larger number of blocks per mqtt request to increase branch coverage. */
#define otaconfigMAX_NUM_BLOCKS_REQUEST         4

#define LOG_LEVEL_ERROR                         0
#define LOG_LEVEL_WARN                          1
#define LOG_LEVEL_INFO                          2
#define LOG_LEVEL_DEBUG                         3

#ifndef LOG_LEVEL
    #define LOG_LEVEL                           -1
#endif

#if LOG_LEVEL >= LOG_LEVEL_ERROR
    #define LogError( msg )    { printf( "[Error] " ); printf msg; printf( "\n" ); }
#endif
#if LOG_LEVEL >= LOG_LEVEL_WARN
    #define LogWarn( msg )     { printf( "[Warn] " ); printf msg; printf( "\n" ); }
#endif
#if LOG_LEVEL >= LOG_LEVEL_INFO
    #define LogInfo( msg )     { printf( "[Info] " ); printf msg; printf( "\n" ); }
#endif
#if LOG_LEVEL >= LOG_LEVEL_DEBUG
    #define LogDebug( msg )    { printf( "[Debug] " ); printf msg; printf( "\n" ); }
#endif

#endif /* _OTA_CONFIG_H_ */
