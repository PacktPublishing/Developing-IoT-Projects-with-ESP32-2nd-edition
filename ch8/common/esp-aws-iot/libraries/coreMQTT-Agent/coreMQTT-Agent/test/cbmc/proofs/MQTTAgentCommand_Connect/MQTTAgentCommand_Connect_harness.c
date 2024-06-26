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
 * @file MQTTAgentCommand_Connect_harness.c
 * @brief Implements the proof harness for MQTTAgentCommand_Connect function.
 */

/* MQTT agent include. */
#include "core_mqtt_agent_command_functions.h"
#include "mqtt_agent_cbmc_state.h"

void harness()
{
    MQTTAgentContext_t * pMqttAgentContext;
    MQTTAgentCommandFuncReturns_t * pReturnFlags;
    MQTTAgentConnectArgs_t * pConnectArgs;

    pMqttAgentContext = malloc( sizeof( MQTTAgentContext_t ) );
    __CPROVER_assume( pMqttAgentContext != NULL );
    pReturnFlags = malloc( sizeof( MQTTAgentCommandFuncReturns_t ) );
    __CPROVER_assume( pReturnFlags != NULL );
    pConnectArgs = allocateConnectArgs( NULL );
    __CPROVER_assume( pConnectArgs != NULL );
    MQTTAgentCommand_Connect( pMqttAgentContext, pConnectArgs, pReturnFlags );
}
