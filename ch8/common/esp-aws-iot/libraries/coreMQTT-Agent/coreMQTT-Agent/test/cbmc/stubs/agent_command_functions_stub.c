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
 * @file agent_command_functions_stub.c
 * @brief Function stubs for processing an MQTT agent command.
 */

/* MQTT Agent command functions include. */
#include "core_mqtt_agent_command_functions.h"

static MQTTStatus_t MQTTAgentCommand_Stub( MQTTAgentContext_t * pMqttAgentContext,
                                           void * pArg,
                                           MQTTAgentCommandFuncReturns_t * pReturnFlags )
{
    MQTTStatus_t returnStatus;
    uint16_t packetId;

    __CPROVER_assert( pMqttAgentContext != NULL, "MQTT Agent context is not NULL." );
    __CPROVER_assert( pReturnFlags != NULL, "Return flags pointer is not NULL." );

    __CPROVER_assume( packetId > 0U );

    pReturnFlags->packetId = packetId;
    pReturnFlags->endLoop = nondet_bool();
    pReturnFlags->addAcknowledgment = nondet_bool();
    pReturnFlags->runProcessLoop = nondet_bool();

    return returnStatus;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTTAgentCommand_ProcessLoop( MQTTAgentContext_t * pMqttAgentContext,
                                           void * pUnusedArg,
                                           MQTTAgentCommandFuncReturns_t * pReturnFlags )
{
    MQTTStatus_t returnStatus;

    returnStatus = MQTTAgentCommand_Stub( pMqttAgentContext,
                                          pUnusedArg,
                                          pReturnFlags );

    pReturnFlags->runProcessLoop = false;
    pReturnFlags->addAcknowledgment = false;

    return returnStatus;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTTAgentCommand_Publish( MQTTAgentContext_t * pMqttAgentContext,
                                       void * pPublishArg,
                                       MQTTAgentCommandFuncReturns_t * pReturnFlags )
{
    MQTTStatus_t returnStatus;
    MQTTPublishInfo_t * pPublishInfo;

    returnStatus = MQTTAgentCommand_Stub( pMqttAgentContext,
                                          pPublishArg,
                                          pReturnFlags );

    if( pPublishArg != NULL )
    {
        pPublishInfo = ( MQTTPublishInfo_t * ) pPublishArg;
        pReturnFlags->addAcknowledgment = ( pPublishInfo->qos > MQTTQoS0 ) ? true : false;
        pReturnFlags->runProcessLoop = ( pPublishInfo->qos > MQTTQoS0 ) ? true : false;
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTTAgentCommand_Subscribe( MQTTAgentContext_t * pMqttAgentContext,
                                         void * pVoidSubscribeArgs,
                                         MQTTAgentCommandFuncReturns_t * pReturnFlags )
{
    MQTTStatus_t returnStatus;

    returnStatus = MQTTAgentCommand_Stub( pMqttAgentContext,
                                          pVoidSubscribeArgs,
                                          pReturnFlags );

    pReturnFlags->addAcknowledgment = true;
    pReturnFlags->runProcessLoop = true;

    return returnStatus;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTTAgentCommand_Unsubscribe( MQTTAgentContext_t * pMqttAgentContext,
                                           void * pVoidSubscribeArgs,
                                           MQTTAgentCommandFuncReturns_t * pReturnFlags )
{
    MQTTStatus_t returnStatus;

    returnStatus = MQTTAgentCommand_Stub( pMqttAgentContext,
                                          pVoidSubscribeArgs,
                                          pReturnFlags );

    pReturnFlags->addAcknowledgment = true;
    pReturnFlags->runProcessLoop = true;

    return returnStatus;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTTAgentCommand_Connect( MQTTAgentContext_t * pMqttAgentContext,
                                       void * pConnectArgs,
                                       MQTTAgentCommandFuncReturns_t * pReturnFlags )
{
    MQTTStatus_t returnStatus;

    returnStatus = MQTTAgentCommand_Stub( pMqttAgentContext,
                                          pConnectArgs,
                                          pReturnFlags );

    pReturnFlags->addAcknowledgment = true;
    pReturnFlags->runProcessLoop = true;

    return returnStatus;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTTAgentCommand_Disconnect( MQTTAgentContext_t * pMqttAgentContext,
                                          void * pUnusedArg,
                                          MQTTAgentCommandFuncReturns_t * pReturnFlags )
{
    MQTTStatus_t returnStatus;

    returnStatus = MQTTAgentCommand_Stub( pMqttAgentContext,
                                          pUnusedArg,
                                          pReturnFlags );

    pReturnFlags->addAcknowledgment = false;
    pReturnFlags->runProcessLoop = false;

    return returnStatus;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTTAgentCommand_Ping( MQTTAgentContext_t * pMqttAgentContext,
                                    void * pUnusedArg,
                                    MQTTAgentCommandFuncReturns_t * pReturnFlags )
{
    MQTTStatus_t returnStatus;

    returnStatus = MQTTAgentCommand_Stub( pMqttAgentContext,
                                          pUnusedArg,
                                          pReturnFlags );

    pReturnFlags->addAcknowledgment = false;
    pReturnFlags->runProcessLoop = false;

    return returnStatus;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTTAgentCommand_Terminate( MQTTAgentContext_t * pMqttAgentContext,
                                         void * pUnusedArg,
                                         MQTTAgentCommandFuncReturns_t * pReturnFlags )
{
    MQTTStatus_t returnStatus;

    returnStatus = MQTTAgentCommand_Stub( pMqttAgentContext,
                                          pUnusedArg,
                                          pReturnFlags );

    pReturnFlags->endLoop = true;

    return returnStatus;
}

/*-----------------------------------------------------------*/
