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
 * @file mqtt_agent_cbmc_state.h
 * @brief Allocation and assumption utilities for the MQTT Agent library CBMC proofs.
 */
#ifndef MQTT_AGENT_CBMC_STATE_H_
#define MQTT_AGENT_CBMC_STATE_H_

#include <stdbool.h>

/* core_mqtt_agent.h must precede including this header. */

/**
 * @brief Allocate a #MQTTFixedBuffer_t object.
 *
 * @param[in] pBuffer #MQTTFixedBuffer_t object information.
 *
 * @return NULL or allocated #MQTTFixedBuffer_t memory.
 */
MQTTFixedBuffer_t * allocateMqttFixedBuffer( MQTTFixedBuffer_t * pFixedBuffer );

/**
 * @brief Validate a #MQTTFixedBuffer_t object.
 *
 * @param[in] pBuffer #MQTTFixedBuffer_t object to validate.
 *
 * @return True if the #MQTTFixedBuffer_t object is valid, false otherwise.
 *
 * @note A NULL object is a valid object. This is for coverage of the NULL
 * parameter checks in the function under proof.
 */
bool isValidMqttFixedBuffer( const MQTTFixedBuffer_t * pFixedBuffer );

/**
 * @brief Allocate a #MQTTAgentContext_t object.
 *
 * @param[in] pContext #MQTTAgentContext_t object information.
 *
 * @return NULL or allocated #MQTTAgentContext_t memory.
 */
MQTTAgentContext_t * allocateMqttAgentContext( MQTTAgentContext_t * pContext );

/**
 * @brief Validate a #MQTTAgentContext_t object.
 *
 * @param[in] pContext #MQTTAgentContext_t object to validate.
 *
 * @return True if the #MQTTAgentContext_t object is valid, false otherwise.
 *
 * @note A NULL object is a valid object. This is for coverage of the NULL
 * parameter checks in the function under proof.
 */
bool isValidMqttAgentContext( const MQTTAgentContext_t * pContext );

/**
 * @brief Function to check if the status is a valid status for the MQTT Agent
 * functions that send a command to the queue. The functions are:
 *  - MQTTAgent_Connect
 *  - MQTTAgent_Disconnect
 *  - MQTTAgent_Subscribe
 *  - MQTTAgent_Unsubscribe
 *  - MQTTAgent_Ping
 *  - MQTTAgent_Publish
 *  - MQTTAgent_ProcessLoop
 *  - MQTTAgent_Terminate
 *
 * @param[in] mqttStatus MQTT status to check if it is a valid MQTTAgent_Connect
 * status.
 *
 * @return true if an MQTTAgent_Connect status, false otherwise.
 */
bool isAgentSendCommandFunctionStatus( MQTTStatus_t mqttStatus );

/**
 * @brief Allocate a #MQTTAgentConnectArgs_t object.
 *
 * @param[in] pConnectArgs #MQTTAgentConnectArgs_t object information.
 *
 * @return NULL or allocated #MQTTAgentConnectArgs_t memory.
 */
MQTTAgentConnectArgs_t * allocateConnectArgs( MQTTAgentConnectArgs_t * pConnectArgs );

/**
 * @brief Add Pending ACKs to the MQTTAgentContext.
 *
 * @param[in] pContext #MQTTAgentContext_t object to add ACKs.
 */
void addPendingAcks( MQTTAgentContext_t * pContext );

/**
 * @brief Allocate a #MQTTAgentSubscribeArgs_t object.
 *
 * @param[in] pSubscribeArgs #MQTTAgentSubscribeArgs_t object information.
 *
 * @return NULL or allocated #MQTTAgentSubscribeArgs_t memory.
 */
MQTTAgentSubscribeArgs_t * allocateSubscribeArgs( MQTTAgentSubscribeArgs_t * pSubscribeArgs );

#endif /* ifndef MQTT_AGENT_CBMC_STATE_H_ */
