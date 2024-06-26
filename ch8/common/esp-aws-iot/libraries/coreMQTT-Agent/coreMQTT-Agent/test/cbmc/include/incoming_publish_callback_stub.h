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
 * @file incoming_publish_callback_stub.h
 * @brief Stub definition for the application defined MQTT library incoming
 * publish callback.
 */
#ifndef INCOMING_PUBLISH_CALLBACK_STUB_H_
#define INCOMING_PUBLISH_CALLBACK_STUB_H_

/* core_mqtt_agent.h must precede including this header. */

/**
 * @brief Callback function called when receiving a publish.
 *
 * @param[in] pMqttAgentContext The context of the MQTT agent.
 * @param[in] packetId The packet ID of the received publish.
 * @param[in] pPublishInfo Deserialized publish information.
 */
void IncomingPublishCallbackStub( MQTTAgentContext_t * pContext,
                                  uint16_t packetId,
                                  MQTTPublishInfo_t * pPublishInfo );

#endif /* ifndef INCOMING_PUBLISH_CALLBACK_STUB_H_ */
