/*
 * coreMQTT Agent v1.2.0
 * Copyright (C) 2021 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * @file incoming_publish_callback_stub.c
 * @brief A stub for the incoming publish callback.
 */

#include "core_mqtt_agent.h"
#include "incoming_publish_callback_stub.h"

void IncomingPublishCallbackStub( MQTTAgentContext_t * pMqttAgentContext,
                                  uint16_t packetId,
                                  MQTTPublishInfo_t * pPublishInfo )
{
    __CPROVER_assert( pMqttAgentContext != NULL,
                      "IncomingPublishCallbackStub pMqttAgentContext is not NULL." );
    __CPROVER_assert( packetId != 0U,
                      "IncomingPublishCallbackStub packetId is not 0." );
    __CPROVER_assert( pPublishInfo != NULL,
                      "IncomingPublishCallbackStub pPublishInfo is not NULL" );
}
