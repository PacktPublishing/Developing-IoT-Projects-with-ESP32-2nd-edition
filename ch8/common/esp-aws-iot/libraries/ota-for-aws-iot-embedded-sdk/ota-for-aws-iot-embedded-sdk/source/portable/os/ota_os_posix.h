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
 * @file ota_os_posix.h
 * @brief Function declarations for the example OTA OS Functional interface for
 * POSIX.
 */

#ifndef _OTA_OS_POSIX_H_
#define _OTA_OS_POSIX_H_

/* Standard library include. */
#include <stdint.h>
#include <time.h>

/* OTA library interface include. */
#include "ota_os_interface.h"

struct OtaTimerContext
{
    timer_t timer;
    OtaTimerId_t timerId;
};

/**
 * @brief Initialize the OTA events.
 *
 * This function initializes the OTA events mechanism for POSIX platforms.
 *
 * @param[pEventCtx]     Pointer to the OTA event context.
 *
 * @return               OtaOsStatus_t, OtaOsSuccess if success , other error code on failure.
 */
OtaOsStatus_t Posix_OtaInitEvent( OtaEventContext_t * pEventCtx );

/**
 * @brief Sends an OTA event.
 *
 * This function sends an event to OTA library event handler for POSIX platforms.
 *
 * @param[pEventCtx]     Pointer to the OTA event context.
 *
 * @param[pEventMsg]     Event to be sent to the OTA handler.
 *
 * @param[timeout]       The maximum amount of time (msec) the task should block.
 *
 * @return               OtaOsStatus_t, OtaOsSuccess if success , other error code on failure.
 */
OtaOsStatus_t Posix_OtaSendEvent( OtaEventContext_t * pEventCtx,
                                  const void * pEventMsg,
                                  unsigned int timeout );

/**
 * @brief Receive an OTA event.
 *
 * This function receives next event from the pending OTA events for POSIX platforms.
 *
 * @param[pEventCtx]     Pointer to the OTA event context.
 *
 * @param[pEventMsg]     Pointer to store message.
 *
 * @param[timeout]       The maximum amount of time the task should block.
 *
 * @return               OtaOsStatus_t, OtaOsSuccess if success , other error code on failure.
 */
OtaOsStatus_t Posix_OtaReceiveEvent( OtaEventContext_t * pEventCtx,
                                     void * pEventMsg,
                                     uint32_t timeout );

/**
 * @brief Deinitialize the OTA Events mechanism.
 *
 * This function deinitialize the OTA events mechanism and frees any resources
 * used on POSIX platforms.
 *
 * @param[pEventCtx]     Pointer to the OTA event context.
 *
 * @return               OtaOsStatus_t, OtaOsSuccess if success , other error code on failure.
 */
OtaOsStatus_t Posix_OtaDeinitEvent( OtaEventContext_t * pEventCtx );


/**
 * @brief Start timer.
 *
 * This function starts the timer or resets it if it is already started for POSIX platforms.
 *
 * @param[otaTimerId]       Timer ID of type otaTimerId_t.
 *
 * @param[pTimerName]       Timer name.
 *
 * @param[timeout]          Timeout for the timer.
 *
 * @param[callback]         Callback to be called when timer expires.
 *
 * @return                  OtaOsStatus_t, OtaOsSuccess if success , other error code on failure.
 */
OtaOsStatus_t Posix_OtaStartTimer( OtaTimerId_t otaTimerId,
                                   const char * const pTimerName,
                                   const uint32_t timeout,
                                   OtaTimerCallback_t callback );

/**
 * @brief Stop timer.
 *
 * This function stops the timer fro POSIX platforms.
 *
 * @param[otaTimerId]     Timer ID of type otaTimerId_t.
 *
 * @return                OtaOsStatus_t, OtaOsSuccess if success , other error code on failure.
 */
OtaOsStatus_t Posix_OtaStopTimer( OtaTimerId_t otaTimerId );

/**
 * @brief Delete a timer.
 *
 * This function deletes a timer for POSIX platforms.
 *
 * @param[otaTimerId]       Timer ID of type otaTimerId_t.
 *
 * @return                  OtaOsStatus_t, OtaOsSuccess if success , other error code on failure.
 */
OtaOsStatus_t Posix_OtaDeleteTimer( OtaTimerId_t otaTimerId );

/**
 * @brief Allocate memory.
 *
 * This function allocates the requested memory and returns a pointer to it using standard
 * C library malloc.
 *
 * @param[size]        This is the size of the memory block, in bytes..
 *
 * @return             This function returns a pointer to the allocated memory, or NULL if
 *                     the request fails.
 */

void * STDC_Malloc( size_t size );

/**
 * @brief Free memory.
 *
 * This function deallocates the memory previously allocated by a call to allocation
 * function of type OtaMalloc_t and uses standard C library free.
 *
 * @param[ptr]         This is the pointer to a memory block previously allocated with function
 *                     of type OtaMalloc_t. If a null pointer is passed as argument, no action occurs.
 *
 * @return             None.
 */

void STDC_Free( void * ptr );

#endif /* ifndef _OTA_OS_POSIX_H_ */
