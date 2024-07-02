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
 * @file ota_os_interface.h
 * @brief Contains OTA OS Functional Interface statuses, type definitions and
 * structures to store interface routines.
 */

#ifndef OTA_OS_INTERFACE_H
#define OTA_OS_INTERFACE_H

/* *INDENT-OFF* */
#ifdef __cplusplus
    extern "C" {
#endif
/* *INDENT-ON* */


/**
 * @otaosfipage
 * @brief The OTA OS Functional Interface definition.
 *
 * @otaosfisectionoverview
 *
 * The OTA OS Functional interface is a set of APIs that must be implemented
 * for the device using the OTA library. The function implementations for this
 * interface are provided to the OTA library in the user application. The OTA
 * library calls the function implementations to perform functionalities that
 * are typically provided by an operating system. This includes managing
 * events, timers, and memory allocation. While these are typically provided by
 * operating systems, an operating system is not required. Any implementation
 * of these functionalities that meet the requirements of the interface will
 * work.
 *
 * The OTA OS Functional Interface is defined in @ref ota_os_interface.h.
 * <br>
 *
 * The functions that must be implemented are:<br>
 * - [OTA OS Functional Interface Initialize Event Mechanism](@ref OtaInitEvent_t)
 * - [OTA OS Functional Interface Send Event](@ref OtaSendEvent_t)
 * - [OTA OS Functional Interface Receive Event](@ref OtaReceiveEvent_t)
 * - [OTA OS Functional Interface Deinitialize Event](@ref OtaDeinitEvent_t)
 * - [OTA OS Functional Interface Timer Callback](@ref OtaTimerCallback_t)
 * - [OTA OS Functional Interface Start Timer](@ref OtaStartTimer_t)
 * - [OTA OS Functional Interface Stop Timer](@ref OtaStopTimer_t)
 * - [OTA OS Functional Interface Delete Timer](@ref OtaDeleteTimer_t)
 * - [OTA OS Functional Interface Malloc](@ref OtaMalloc_t)
 * - [OTA OS Functional Interface Free](@ref OtaFree_t)
 *
 * An example implementation for the OTA OS Functional Interface for FreeRTOS
 * can be found in the files ota_os_freertos.c and ota_os_freertos.h.
 *
 * An example implementation for the OTA OS Functional Interface for POSIX can
 * be found in the files ota_os_posix.c and ota_os_posix.h.
 */

struct OtaEventContext;

/**
 * @brief Type definition for Event Context.
 */
typedef struct OtaEventContext OtaEventContext_t;

/**
 * @brief Enumeration for tracking multiple timers.
 */
typedef enum
{
    OtaRequestTimer = 0,
    OtaSelfTestTimer,
    OtaNumOfTimers
} OtaTimerId_t;

/**
 * @ingroup ota_enum_types
 * @brief The OTA OS interface return status.
 */
typedef enum OtaOsStatus
{
    OtaOsSuccess = 0,                    /*!< @brief OTA OS interface success. */
    OtaOsEventQueueCreateFailed = 0x80U, /*!< @brief Failed to create the event queue. */
    OtaOsEventQueueSendFailed,           /*!< @brief Posting event message to the event queue failed. */
    OtaOsEventQueueReceiveFailed,        /*!< @brief Failed to receive from the event queue. */
    OtaOsEventQueueDeleteFailed,         /*!< @brief Failed to delete the event queue. */
    OtaOsTimerCreateFailed,              /*!< @brief Failed to create the timer. */
    OtaOsTimerStartFailed,               /*!< @brief Failed to create the timer. */
    OtaOsTimerRestartFailed,             /*!< @brief Failed to restart the timer. */
    OtaOsTimerStopFailed,                /*!< @brief Failed to stop the timer. */
    OtaOsTimerDeleteFailed               /*!< @brief Failed to delete the timer. */
} OtaOsStatus_t;

/**
 * @brief Initialize the OTA events.
 *
 * This function initializes the OTA events mechanism.
 *
 * @param[pEventCtx]     Pointer to the OTA event context.
 *
 * @return               OtaOsStatus_t, OtaOsSuccess if success , other error code on failure.
 */

typedef OtaOsStatus_t ( * OtaInitEvent_t ) ( OtaEventContext_t * pEventCtx );

/**
 * @brief Sends an OTA event.
 *
 * This function sends an event to OTA library event handler.
 *
 * @param[pEventCtx]     Pointer to the OTA event context.
 *
 * @param[pEventMsg]     Event to be sent to the OTA handler.
 *
 * @param[timeout]       The maximum amount of time (msec) the task should block.
 *
 * @return               OtaOsStatus_t, OtaOsSuccess if success , other error code on failure.
 */

typedef OtaOsStatus_t ( * OtaSendEvent_t )( OtaEventContext_t * pEventCtx,
                                            const void * pEventMsg,
                                            unsigned int timeout );

/**
 * @brief Receive an OTA event.
 *
 * This function receives next event from the pending OTA events.
 *
 * @param[pEventCtx]     Pointer to the OTA event context.
 *
 * @param[pEventMsg]     Pointer to store message.
 *
 * @param[timeout]       The maximum amount of time (msec) the task should block.
 *
 * @return               OtaOsStatus_t, OtaOsSuccess if success , other error code on failure.
 */

typedef OtaOsStatus_t ( * OtaReceiveEvent_t )( OtaEventContext_t * pEventCtx,
                                               void * pEventMsg,
                                               uint32_t timeout );

/**
 * @brief Deinitialize the OTA Events mechanism.
 *
 * This function deinitialize the OTA events mechanism and frees any resources
 * used.
 *
 * @param[pEventCtx]     Pointer to the OTA event context.
 *
 * @return               OtaOsStatus_t, OtaOsSuccess if success , other error code on failure.
 */

typedef OtaOsStatus_t ( * OtaDeinitEvent_t )( OtaEventContext_t * pEventCtx );

/**
 * @brief Timer callback.
 *
 * Type definition for timer callback.
 *
 * @param[otaTimerId]       Timer ID of type otaTimerId_t
 *
 * @return                  OtaOsStatus_t, OtaOsSuccess if success , other error code on failure.
 */

typedef void ( * OtaTimerCallback_t )( OtaTimerId_t otaTimerId );

/**
 * @brief Start timer.
 *
 * This function starts the timer or resets it if it has already started.
 *
 * @param[otaTimerId]       Timer ID of type otaTimerId_t
 *
 * @param[pTimerName]       Timer name.
 *
 * @param[timeout]          Timeout for the timer in milliseconds.
 *
 * @param[callback]         Callback to be called when timer expires.
 *
 * @return                  OtaOsStatus_t, OtaOsSuccess if success , other error code on failure.
 */

typedef OtaOsStatus_t ( * OtaStartTimer_t ) ( OtaTimerId_t otaTimerId,
                                              const char * const pTimerName,
                                              const uint32_t timeout,
                                              OtaTimerCallback_t callback );

/**
 * @brief Stop timer.
 *
 * This function stops the time.
 *
 * @param[otaTimerId]     Timer ID of type otaTimerId_t
 *
 * @return                OtaOsStatus_t, OtaOsSuccess if success , other error code on failure.
 */

typedef OtaOsStatus_t ( * OtaStopTimer_t ) ( OtaTimerId_t otaTimerId );

/**
 * @brief Delete a timer.
 *
 * This function deletes a timer.
 *
 * @param[otaTimerId]       Timer ID of type otaTimerId_t
 *
 * @return                  OtaOsStatus_t, OtaOsSuccess if success , other error code on failure.
 */

typedef OtaOsStatus_t ( * OtaDeleteTimer_t ) ( OtaTimerId_t otaTimerId );

/**
 * @brief Allocate memory.
 *
 * This function allocates the requested memory and returns a pointer to it.
 *
 * @param[size]        This is the size of the memory block, in bytes..
 *
 * @return             This function returns a pointer to the allocated memory, or NULL if
 *                     the request fails.
 */

typedef void * ( * OtaMalloc_t ) ( size_t size );

/**
 * @brief Free memory.
 *
 * This function deallocates the memory previously allocated by a call to allocation
 * function of type OtaMalloc_t.
 *
 * @param[ptr]         This is the pointer to a memory block previously allocated with function
 *                     of type OtaMalloc_t. If a null pointer is passed as argument, no action occurs.
 *
 * @return             None.
 */

typedef void ( * OtaFree_t ) ( void * ptr );

/**
 * @ingroup ota_struct_types
 * OTA Event Interface structure.
 */
typedef struct OtaEventInterface
{
    OtaInitEvent_t init;               /*!< @brief Initialization event. */
    OtaSendEvent_t send;               /*!< @brief Send data. */
    OtaReceiveEvent_t recv;            /*!< @brief Receive data. */
    OtaDeinitEvent_t deinit;           /*!< @brief Deinitialize event. */
    OtaEventContext_t * pEventContext; /*!< @brief Event context to store event information. */
} OtaEventInterface_t;

/**
 * @ingroup ota_struct_types
 * @brief OTA Retry Timer Interface.
 */
typedef struct OtaTimerInterface
{
    OtaStartTimer_t start;            /*!< @brief Timer start state. */
    OtaStopTimer_t stop;              /*!< @brief Timer stop state. */
    #ifndef __cplusplus
        OtaDeleteTimer_t delete;      /*!< @brief Delete timer. */
    #else
        OtaDeleteTimer_t deleteTimer; /*!< @brief Delete timer for C++ builds. */
    #endif
} OtaTimerInterface_t;

/**
 * @ingroup ota_struct_types
 * @brief OTA memory allocation interface.
 */
typedef struct OtaMallocInterface
{
    /* MISRA Ref 21.3.2 [Use of free or malloc] */
    /* More details at: https://github.com/aws/ota-for-aws-iot-embedded-sdk/blob/main/MISRA.md#rule-213 */
    /* coverity[misra_c_2012_rule_21_3_violation] */
    OtaMalloc_t malloc; /*!< @brief OTA memory allocate interface. */
    /* MISRA Ref 21.3.2 [Use of free or malloc] */
    /* More details at: https://github.com/aws/ota-for-aws-iot-embedded-sdk/blob/main/MISRA.md#rule-213 */
    /* coverity[misra_c_2012_rule_21_3_violation] */
    OtaFree_t free; /*!< @brief OTA memory deallocate interface. */
} OtaMallocInterface_t;

/**
 * @ingroup ota_struct_types
 * @brief  OTA OS Interface.
 */
typedef struct OtaOSInterface
{
    OtaEventInterface_t event; /*!< @brief OTA Event interface. */
    OtaTimerInterface_t timer; /*!< @brief OTA Timer interface. */
    OtaMallocInterface_t mem;  /*!< @brief OTA memory interface. */
} OtaOSInterface_t;

/* *INDENT-OFF* */
#ifdef __cplusplus
    }
#endif
/* *INDENT-ON* */

#endif /* ifndef OTA_OS_INTERFACE_H */
