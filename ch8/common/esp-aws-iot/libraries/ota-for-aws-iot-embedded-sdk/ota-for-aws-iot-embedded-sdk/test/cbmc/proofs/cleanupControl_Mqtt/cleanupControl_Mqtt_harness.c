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
 * @file cleanupControl_Mqtt_harness.c
 * @brief Implements the proof harness for cleanupControl_Mqtt function.
 */
/* Include headers for mqtt interface. */
#include "ota_mqtt_private.h"

/* Stub required to unsubscribe from a job notification topic function. */
OtaMqttStatus_t __CPROVER_file_local_ota_mqtt_c_unsubscribeFromJobNotificationTopic( const OtaAgentContext_t * pAgentCtx )
{
    OtaMqttStatus_t mqttStatus;

    /* Since OTA agent is initialized before passing to unsubscribeFromJobNotificationTopic,
     * pAgentCtx is expected to be a non-NULL value. */
    __CPROVER_assert( pAgentCtx != NULL, "Unable to use pAgentCtx:"
                                         "Expected a non-NULL value." );

    return mqttStatus;
}

void cleanupControl_Mqtt_harness()
{
    OtaAgentContext_t agent;

    /* OTA agent is declared as a global variable in ota.c and thus cannot be NULL. */
    ( void ) cleanupControl_Mqtt( &agent );
}
