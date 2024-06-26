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
 * @file core_mqtt_agent_command_functions.c
 * @brief Implements functions to process MQTT agent commands.
 */

/* Standard includes. */
#include <string.h>
#include <stdio.h>
#include <assert.h>

/* MQTT agent include. */
#include "core_mqtt_agent.h"

/* Header include. */
#include "core_mqtt_agent_command_functions.h"

/* MQTT Agent default logging configuration include. */
#include "core_mqtt_agent_default_logging.h"

/*-----------------------------------------------------------*/

MQTTStatus_t MQTTAgentCommand_ProcessLoop( MQTTAgentContext_t * pMqttAgentContext,
                                           void * pUnusedArg,
                                           MQTTAgentCommandFuncReturns_t * pReturnFlags )
{
    ( void ) pUnusedArg;
    ( void ) pMqttAgentContext;
    assert( pReturnFlags != NULL );

    ( void ) memset( pReturnFlags, 0x00, sizeof( MQTTAgentCommandFuncReturns_t ) );
    pReturnFlags->runProcessLoop = true;

    return MQTTSuccess;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTTAgentCommand_Publish( MQTTAgentContext_t * pMqttAgentContext,
                                       void * pPublishArg,
                                       MQTTAgentCommandFuncReturns_t * pReturnFlags )
{
    const MQTTPublishInfo_t * pPublishInfo;
    MQTTStatus_t ret;

    assert( pMqttAgentContext != NULL );
    assert( pPublishArg != NULL );
    assert( pReturnFlags != NULL );

    ( void ) memset( pReturnFlags, 0x00, sizeof( MQTTAgentCommandFuncReturns_t ) );
    pPublishInfo = ( const MQTTPublishInfo_t * ) ( pPublishArg );

    if( pPublishInfo->qos != MQTTQoS0 )
    {
        pReturnFlags->packetId = MQTT_GetPacketId( &( pMqttAgentContext->mqttContext ) );
    }

    LogInfo( ( "Publishing message to %.*s.\n", ( int ) pPublishInfo->topicNameLength, pPublishInfo->pTopicName ) );
    ret = MQTT_Publish( &( pMqttAgentContext->mqttContext ), pPublishInfo, pReturnFlags->packetId );

    /* Add to pending ack list, or call callback if QoS 0. */
    pReturnFlags->addAcknowledgment = ( pPublishInfo->qos != MQTTQoS0 ) && ( ret == MQTTSuccess );
    pReturnFlags->runProcessLoop = true;

    return ret;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTTAgentCommand_Subscribe( MQTTAgentContext_t * pMqttAgentContext,
                                         void * pVoidSubscribeArgs,
                                         MQTTAgentCommandFuncReturns_t * pReturnFlags )
{
    const MQTTAgentSubscribeArgs_t * pSubscribeArgs;
    MQTTStatus_t ret;

    assert( pMqttAgentContext != NULL );
    assert( pVoidSubscribeArgs != NULL );
    assert( pReturnFlags != NULL );

    ( void ) memset( pReturnFlags, 0x00, sizeof( MQTTAgentCommandFuncReturns_t ) );
    pSubscribeArgs = ( const MQTTAgentSubscribeArgs_t * ) ( pVoidSubscribeArgs );
    pReturnFlags->packetId = MQTT_GetPacketId( &( pMqttAgentContext->mqttContext ) );

    ret = MQTT_Subscribe( &( pMqttAgentContext->mqttContext ),
                          pSubscribeArgs->pSubscribeInfo,
                          pSubscribeArgs->numSubscriptions,
                          pReturnFlags->packetId );

    pReturnFlags->addAcknowledgment = ( ret == MQTTSuccess );
    pReturnFlags->runProcessLoop = true;

    return ret;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTTAgentCommand_Unsubscribe( MQTTAgentContext_t * pMqttAgentContext,
                                           void * pVoidSubscribeArgs,
                                           MQTTAgentCommandFuncReturns_t * pReturnFlags )
{
    const MQTTAgentSubscribeArgs_t * pSubscribeArgs;
    MQTTStatus_t ret;

    assert( pMqttAgentContext != NULL );
    assert( pVoidSubscribeArgs != NULL );
    assert( pReturnFlags != NULL );

    ( void ) memset( pReturnFlags, 0x00, sizeof( MQTTAgentCommandFuncReturns_t ) );
    pSubscribeArgs = ( const MQTTAgentSubscribeArgs_t * ) ( pVoidSubscribeArgs );
    pReturnFlags->packetId = MQTT_GetPacketId( &( pMqttAgentContext->mqttContext ) );

    ret = MQTT_Unsubscribe( &( pMqttAgentContext->mqttContext ),
                            pSubscribeArgs->pSubscribeInfo,
                            pSubscribeArgs->numSubscriptions,
                            pReturnFlags->packetId );

    pReturnFlags->addAcknowledgment = ( ret == MQTTSuccess );
    pReturnFlags->runProcessLoop = true;

    return ret;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTTAgentCommand_Connect( MQTTAgentContext_t * pMqttAgentContext,
                                       void * pVoidConnectArgs,
                                       MQTTAgentCommandFuncReturns_t * pReturnFlags )
{
    MQTTStatus_t ret;
    MQTTAgentConnectArgs_t * pConnectInfo;

    assert( pMqttAgentContext != NULL );
    assert( pVoidConnectArgs != NULL );
    assert( pReturnFlags != NULL );

    pConnectInfo = ( MQTTAgentConnectArgs_t * ) ( pVoidConnectArgs );

    ret = MQTT_Connect( &( pMqttAgentContext->mqttContext ),
                        pConnectInfo->pConnectInfo,
                        pConnectInfo->pWillInfo,
                        pConnectInfo->timeoutMs,
                        &( pConnectInfo->sessionPresent ) );

    /* Resume a session if one existed, else clear the list of acknowledgments. */
    if( ret == MQTTSuccess )
    {
        LogInfo( ( "Session present flag: %d", pConnectInfo->sessionPresent ) );
        ret = MQTTAgent_ResumeSession( pMqttAgentContext,
                                       pConnectInfo->sessionPresent );
    }

    ( void ) memset( pReturnFlags, 0x00, sizeof( MQTTAgentCommandFuncReturns_t ) );

    return ret;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTTAgentCommand_Disconnect( MQTTAgentContext_t * pMqttAgentContext,
                                          void * pUnusedArg,
                                          MQTTAgentCommandFuncReturns_t * pReturnFlags )
{
    MQTTStatus_t ret;

    ( void ) pUnusedArg;

    assert( pMqttAgentContext != NULL );
    assert( pReturnFlags != NULL );

    ret = MQTT_Disconnect( &( pMqttAgentContext->mqttContext ) );

    ( void ) memset( pReturnFlags, 0x00, sizeof( MQTTAgentCommandFuncReturns_t ) );
    pReturnFlags->endLoop = true;

    return ret;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTTAgentCommand_Ping( MQTTAgentContext_t * pMqttAgentContext,
                                    void * pUnusedArg,
                                    MQTTAgentCommandFuncReturns_t * pReturnFlags )
{
    MQTTStatus_t ret;

    ( void ) pUnusedArg;

    assert( pMqttAgentContext != NULL );
    assert( pReturnFlags != NULL );

    ret = MQTT_Ping( &( pMqttAgentContext->mqttContext ) );

    ( void ) memset( pReturnFlags, 0x00, sizeof( MQTTAgentCommandFuncReturns_t ) );

    pReturnFlags->runProcessLoop = true;

    return ret;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTTAgentCommand_Terminate( MQTTAgentContext_t * pMqttAgentContext,
                                         void * pUnusedArg,
                                         MQTTAgentCommandFuncReturns_t * pReturnFlags )
{
    MQTTStatus_t ret;

    ( void ) pUnusedArg;

    assert( pMqttAgentContext != NULL );
    assert( pMqttAgentContext->agentInterface.releaseCommand != NULL );
    assert( pReturnFlags != NULL );

    LogInfo( ( "Terminating command loop.\n" ) );
    ( void ) memset( pReturnFlags, 0x00, sizeof( MQTTAgentCommandFuncReturns_t ) );
    pReturnFlags->endLoop = true;

    ret = MQTTAgent_CancelAll( pMqttAgentContext );

    return ret;
}

/*-----------------------------------------------------------*/
