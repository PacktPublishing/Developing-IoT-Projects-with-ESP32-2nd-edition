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
 * @file ota_os_posix_utest.c
 * @brief Unit tests for functions in ota_os_posix.c
 */

#include <string.h>
#include <mqueue.h>
#include <unistd.h>
#include "unity.h"

/* For accessing OTA private functions and error codes. */
#include "ota.h"
#include "ota_os_posix.h"

/* Testing constants. */
#define TIMER_NAME             "dummy_name"
#define OTA_DEFAULT_TIMEOUT    1000 /*!< Timeout in milliseconds. */
#define NS_TO_S( ns )    ( ns / 1000000000.0 )

/* Interfaces for Timer and Event. */
static OtaTimerInterface_t timer;
static OtaEventInterface_t event;
static OtaEventContext_t * pEventContext = NULL;
static bool timerCallbackInovked = false;

static void timerCallback()
{
    timerCallbackInovked = true;
}
/* ============================   UNITY FIXTURES ============================ */

void setUp( void )
{
    timer.start = Posix_OtaStartTimer;
    timer.delete = Posix_OtaDeleteTimer;
    timer.stop = Posix_OtaStopTimer;

    event.init = Posix_OtaInitEvent;
    event.send = Posix_OtaSendEvent;
    event.recv = Posix_OtaReceiveEvent;
    event.deinit = Posix_OtaDeinitEvent;
    event.pEventContext = pEventContext;
}

void tearDown( void )
{
    timerCallbackInovked = false;
}

/* ========================================================================== */

/**
 * @brief Test that the event queue gets populated with the messages.
 */
void test_OTA_posix_SendAndRecvEvent( void )
{
    OtaEventMsg_t otaEventToSend = { 0 };
    OtaEventMsg_t otaEventToRecv = { 0 };
    OtaErr_t result = OtaErrUninitialized;

    otaEventToSend.eventId = OtaAgentEventStart;
    result = event.init( event.pEventContext );
    TEST_ASSERT_EQUAL( OtaErrNone, result );

    result = event.send( event.pEventContext, &otaEventToSend, 0 );
    TEST_ASSERT_EQUAL( OtaErrNone, result );
    result = event.recv( event.pEventContext, &otaEventToRecv, 0 );
    TEST_ASSERT_EQUAL( OtaErrNone, result );
    TEST_ASSERT_EQUAL( otaEventToSend.eventId, otaEventToRecv.eventId );

    result = event.deinit( event.pEventContext );
    TEST_ASSERT_EQUAL( OtaErrNone, result );
}

/**
 * @brief Test that the event queue operations do not succeed for invalid operations.
 */
void test_OTA_posix_InvalidEventQueue( void )
{
    OtaErr_t result = OtaErrUninitialized;

    result = event.init( event.pEventContext );
    TEST_ASSERT_EQUAL( OtaErrNone, result );

    result = event.deinit( event.pEventContext );
    TEST_ASSERT_EQUAL( OtaErrNone, result );

    /* Try to deinitialize a non-existing queue. */
    result = event.deinit( event.pEventContext );
    TEST_ASSERT_EQUAL( OtaOsEventQueueDeleteFailed, result );
}

void timerCreateAndStop( OtaTimerId_t timer_id )
{
    OtaErr_t result = OtaErrUninitialized;
    int wait = 2 * OTA_DEFAULT_TIMEOUT; /* Wait for 2 times of the timeout specified. */

    result = timer.start( timer_id, TIMER_NAME, OTA_DEFAULT_TIMEOUT, timerCallback );
    TEST_ASSERT_EQUAL( OtaErrNone, result );

    /* Wait for the timer callback to be invoked. */
    while( timerCallbackInovked == false && wait > 0 )
    {
        /* Sleep 1 ms. */
        usleep( 1000 );
        --wait;
    }

    TEST_ASSERT_EQUAL( true, timerCallbackInovked );

    result = timer.stop( timer_id );
    TEST_ASSERT_EQUAL( OtaErrNone, result );

    result = timer.delete( timer_id );
    TEST_ASSERT_EQUAL( OtaErrNone, result );
}

/**
 * @brief Test timers are initialized, stopped and deleted successfully.
 */
void test_OTA_posix_RequestTimerCreateAndStop( void )
{
    timerCreateAndStop( OtaRequestTimer );
}

/**
 * @brief Test timers are initialized, stopped and deleted successfully.
 */
void test_OTA_posix_SelfTestTimerCreateAndStop( void )
{
    timerCreateAndStop( OtaSelfTestTimer );
}

/**
 * @brief Test invalid operations on timers.
 */
void test_OTA_posix_InvalidTimerOperations( void )
{
    OtaErr_t result = OtaErrUninitialized;
    OtaTimerId_t timer_id = OtaRequestTimer;

    result = timer.start( timer_id, TIMER_NAME, OTA_DEFAULT_TIMEOUT, NULL );
    TEST_ASSERT_EQUAL( OtaErrNone, result );

    /* Set the timeout to 0 and stop the timer*/
    result = timer.start( timer_id, TIMER_NAME, 0, NULL );
    TEST_ASSERT_EQUAL( OtaErrNone, result );

    result = timer.stop( timer_id );
    TEST_ASSERT_EQUAL( OtaErrNone, result );

    result = timer.delete( timer_id );
    TEST_ASSERT_EQUAL( OtaErrNone, result );

    /* Delete a timer that has been deleted. */
    result = timer.delete( timer_id );
    TEST_ASSERT_NOT_EQUAL( OtaErrNone, result );
}

/**
 * @brief Test memory allocation and free.
 */
void test_OTA_posix_MemoryAllocAndFree( void )
{
    uint8_t * buffer = NULL;

    buffer = ( uint8_t * ) STDC_Malloc( sizeof( uint8_t ) );
    TEST_ASSERT_NOT_NULL( buffer );

    /* Test that we can access and assign a value in the buffer. */
    memset( buffer, 1, 1 );
    TEST_ASSERT_EQUAL( 1, *buffer );

    STDC_Free( buffer );
}

/**
 * @brief Test that the event queue receive timeout.
 */
void test_OTA_posix_RecvEventTimeout( void )
{
    OtaEventMsg_t otaEventToRecv = { 0 };
    OtaErr_t result = OtaErrUninitialized;
    time_t recvTimeoutMs = 3000;
    struct timespec tsStartTime = { 0 };
    struct timespec tsEndTime = { 0 };
    double timeDiffSec = 0;

    result = event.init( event.pEventContext );
    TEST_ASSERT_EQUAL( OtaErrNone, result );

    ( void ) clock_gettime( CLOCK_MONOTONIC, &tsStartTime );
    result = event.recv( event.pEventContext, &otaEventToRecv, recvTimeoutMs );
    TEST_ASSERT_EQUAL( OtaOsEventQueueReceiveFailed, result );
    ( void ) clock_gettime( CLOCK_MONOTONIC, &tsEndTime );

    /* Get time duration. */
    if( tsEndTime.tv_nsec - tsStartTime.tv_nsec < 0 )
    {
        timeDiffSec = tsEndTime.tv_sec - tsStartTime.tv_sec - 1;
        timeDiffSec += NS_TO_S( ( double ) ( 1000000000 + tsEndTime.tv_nsec - tsStartTime.tv_nsec ) );
    }
    else
    {
        timeDiffSec = tsEndTime.tv_sec - tsStartTime.tv_sec;
        timeDiffSec += NS_TO_S( ( double ) ( tsEndTime.tv_nsec - tsStartTime.tv_nsec ) );
    }

    /* The time may not accurate enough, so - 1 as buffer. */
    TEST_ASSERT_GREATER_OR_EQUAL( ( recvTimeoutMs / 1000 ) - 1, timeDiffSec );

    result = event.deinit( event.pEventContext );
    TEST_ASSERT_EQUAL( OtaErrNone, result );
}
