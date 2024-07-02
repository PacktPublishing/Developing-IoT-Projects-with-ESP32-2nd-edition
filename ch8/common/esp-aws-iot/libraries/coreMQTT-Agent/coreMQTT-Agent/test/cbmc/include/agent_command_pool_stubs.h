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
 * @file agent_command_pool_stubs.h
 * @brief Stub functions to get and release command structure from a command pool.
 */
#ifndef AGENT_COMMAND_POOL_STUBS_H
#define AGENT_COMMAND_POOL_STUBS_H

#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>

/* core_mqtt_agent.h must precede including this header. */

/**
 * @brief Send a message to the specified context.
 *
 * @param[in] blockTimeMs The length of time the calling task should remain in the
 * Blocked state (so not consuming any CPU time) to wait for a MQTTAgentCommand_t structure to
 * become available should one not be immediately at the time of the call.
 *
 * @return A pointer to a MQTTAgentCommand_t structure if one becomes available before
 * blockTimeMs time expired, otherwise NULL.
 */
MQTTAgentCommand_t * AgentGetCommandStub( uint32_t blockTimeMs );

/**
 * @brief Receive a message from the specified context.
 * Must be thread safe.
 *
 * @param[in] pCommandToRelease A pointer to the MQTTAgentCommand_t structure to return to
 * the pool.  The structure must first have been obtained by calling
 * Agent_GetCommand(), otherwise Agent_ReleaseCommand() will
 * have no effect.
 *
 * @return true if the MQTTAgentCommand_t structure was returned to the pool, otherwise false.
 */
bool Agent_ReleaseCommand( MQTTAgentCommand_t * pCommandToRelease );

#endif /* AGENT_COMMAND_POOL_STUBS_H */
