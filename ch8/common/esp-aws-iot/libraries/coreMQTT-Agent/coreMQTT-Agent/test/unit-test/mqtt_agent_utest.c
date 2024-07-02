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
 * @file mqtt_agent_utest.c
 * @brief Unit tests for functions in mqtt_agent_utest.h
 */
#include <string.h>
#include <stdbool.h>

#include "unity.h"

/* Include paths for public enums, structures, and macros. */
#include "core_mqtt_agent.h"
#include "mock_core_mqtt.h"
#include "mock_core_mqtt_state.h"
#include "mock_core_mqtt_agent_command_functions.h"


/**
 * @brief The agent messaging context.
 */
struct MQTTAgentMessageContext
{
    MQTTAgentCommand_t * pSentCommand;
};

/**
 * @brief Command callback context.
 */
struct MQTTAgentCommandContext
{
    MQTTStatus_t returnStatus;
};

/**
 * @brief Time at the beginning of each test. Note that this is not updated with
 * a real clock. Instead, we simply increment this variable.
 */
static uint32_t globalEntryTime = 0;

/**
 * @brief The number of times the release command function is called.
 */
static uint32_t commandReleaseCallCount = 0;

/**
 * @brief Message context to use for tests.
 */
static MQTTAgentMessageContext_t globalMessageContext;

/**
 * @brief Command struct pointer to return from mocked getCommand.
 */
static MQTTAgentCommand_t * pCommandToReturn;

/**
 * @brief Mock Counter variable to check callback is called on command completion.
 */
static uint32_t commandCompleteCallbackCount;

/**
 * @brief Mock Counter variable to check callback is called when incoming publish is received.
 */
static uint32_t publishCallbackCount;

/**
 * @brief Mock packet type to be used for testing all the received packet types via mqttEventcallback.
 */
static uint8_t packetType;

/**
 * @brief Mock packet identifier to be used for acknowledging received packets via mqttEventcallback.
 */
static uint16_t packetIdentifier;

/**
 * @brief Mock Counter variable for calling stubReceiveThenFail multiple times.
 */
static uint32_t receiveCounter;

/**
 * @brief Return flags to use for test.
 */
static MQTTAgentCommandFuncReturns_t returnFlags;

/* ============================   UNITY FIXTURES ============================ */

/* Called before each test method. */
void setUp()
{
    globalEntryTime = 0;
    commandReleaseCallCount = 0;
    publishCallbackCount = 0;
    globalMessageContext.pSentCommand = NULL;
    pCommandToReturn = NULL;
    commandCompleteCallbackCount = 0;
    packetIdentifier = 1U;
    receiveCounter = 0;
    returnFlags.addAcknowledgment = false;
    returnFlags.runProcessLoop = false;
    returnFlags.endLoop = false;
}

/* Called after each test method. */
void tearDown()
{
}

/* Called at the beginning of the whole suite. */
void suiteSetUp()
{
}

/* Called at the end of the whole suite. */
int suiteTearDown( int numFailures )
{
    return numFailures;
}

/* ========================================================================== */

/**
 * @brief A mocked send function to send commands to the agent.
 */
static bool stubSend( MQTTAgentMessageContext_t * pMsgCtx,
                      MQTTAgentCommand_t * const * pCommandToSend,
                      uint32_t blockTimeMs )
{
    ( void ) blockTimeMs;
    pMsgCtx->pSentCommand = *pCommandToSend;
    return true;
}

/**
 * @brief A mocked send function to send commands to the agent.
 * Returns failure.
 */
static bool stubSendFail( MQTTAgentMessageContext_t * pMsgCtx,
                          MQTTAgentCommand_t * const * pCommandToSend,
                          uint32_t blockTimeMs )
{
    ( void ) pMsgCtx;
    ( void ) pCommandToSend;
    ( void ) blockTimeMs;
    return false;
}

/**
 * @brief A mocked receive function for the agent to receive commands.
 */
static bool stubReceive( MQTTAgentMessageContext_t * pMsgCtx,
                         MQTTAgentCommand_t ** pReceivedCommand,
                         uint32_t blockTimeMs )
{
    ( void ) blockTimeMs;
    *pReceivedCommand = pMsgCtx->pSentCommand;
    return true;
}

/**
 * @brief A mocked receive function for the agent to receive commands.
 */
static bool stubReceiveThenFail( MQTTAgentMessageContext_t * pMsgCtx,
                                 MQTTAgentCommand_t ** pReceivedCommand,
                                 uint32_t blockTimeMs )
{
    bool ret = false;

    ( void ) blockTimeMs;

    if( receiveCounter++ == 0 )
    {
        *pReceivedCommand = pMsgCtx->pSentCommand;
        ret = true;
    }

    return ret;
}

/**
 * @brief A mocked function to obtain an allocated command.
 */
static MQTTAgentCommand_t * stubGetCommand( uint32_t blockTimeMs )
{
    ( void ) blockTimeMs;
    return pCommandToReturn;
}

/**
 * @brief A mocked function to release an allocated command.
 */
static bool stubReleaseCommand( MQTTAgentCommand_t * pCommandToRelease )
{
    ( void ) pCommandToRelease;
    commandReleaseCallCount++;
    return true;
}

/**
 * @brief A mock publish callback function.
 */
static void stubPublishCallback( MQTTAgentContext_t * pMqttAgentContext,
                                 uint16_t packetId,
                                 MQTTPublishInfo_t * pPublishInfo )
{
    ( void ) pMqttAgentContext;
    ( void ) packetId;
    ( void ) pPublishInfo;

    publishCallbackCount++;
}

static void stubCompletionCallback( MQTTAgentCommandContext_t * pCommandCompletionContext,
                                    MQTTAgentReturnInfo_t * pReturnInfo )
{
    if( pCommandCompletionContext != NULL )
    {
        pCommandCompletionContext->returnStatus = pReturnInfo->returnCode;
    }

    commandCompleteCallbackCount++;
}

/**
 * @brief A mocked timer query function that increments on every call.
 */
static uint32_t stubGetTime( void )
{
    return globalEntryTime++;
}

/**
 * @brief A stub for MQTT_Init function to be used to initialize the event callback.
 */
static MQTTStatus_t MQTT_Init_CustomStub( MQTTContext_t * pContext,
                                          const TransportInterface_t * pTransport,
                                          MQTTGetCurrentTimeFunc_t getTimeFunc,
                                          MQTTEventCallback_t userCallback,
                                          const MQTTFixedBuffer_t * pNetworkBuffer,
                                          int numCalls )
{
    ( void ) numCalls;

    pContext->connectStatus = MQTTNotConnected;
    pContext->transportInterface = *pTransport;
    pContext->getTime = getTimeFunc;
    pContext->appCallback = userCallback;
    pContext->networkBuffer = *pNetworkBuffer;
    pContext->nextPacketId = 1;
    return MQTTSuccess;
}

/**
 * @brief A stub for MQTT_ProcessLoop function to be used to test the event callback.
 */
MQTTStatus_t MQTT_ProcessLoop_CustomStub( MQTTContext_t * pContext,
                                          int numCalls )
{
    MQTTPacketInfo_t packetInfo = { 0 };
    MQTTDeserializedInfo_t deserializedInfo = { 0 };
    MQTTAgentContext_t * pMqttAgentContext;

    ( void ) numCalls;

    packetInfo.type = packetType;
    deserializedInfo.packetIdentifier = packetIdentifier;

    pContext->appCallback( pContext, &packetInfo, &deserializedInfo );
    pMqttAgentContext = ( MQTTAgentContext_t * ) pContext;
    pMqttAgentContext->packetReceivedInLoop = false;

    return MQTTSuccess;
}

/**
 * @brief A stub for MQTT_ProcessLoop function to be used to test the event callback.
 */
MQTTStatus_t MQTT_ProcessLoop_NeedMoreBytes( MQTTContext_t * pContext,
                                             int numCalls )
{
    MQTTAgentContext_t * pMqttAgentContext;

    pMqttAgentContext = ( MQTTAgentContext_t * ) pContext;

    if( numCalls == 0 )
    {
        pMqttAgentContext->packetReceivedInLoop = true;
    }
    else
    {
        pMqttAgentContext->packetReceivedInLoop = false;
    }

    return MQTTNeedMoreBytes;
}

/**
 * @brief A stub for MQTT_ProcessLoop function which fails on second and later calls.
 */
MQTTStatus_t MQTT_ProcessLoop_FailSecondAndLaterCallsStub( MQTTContext_t * pContext,
                                                           int numCalls )
{
    MQTTPacketInfo_t packetInfo;
    MQTTDeserializedInfo_t deserializedInfo;
    MQTTStatus_t status;

    packetInfo.type = packetType;
    deserializedInfo.packetIdentifier = packetIdentifier;

    if( numCalls == 0 )
    {
        pContext->appCallback( pContext, &packetInfo, &deserializedInfo );
        status = MQTTSuccess;
    }
    else
    {
        /* MQTT_ProcessLoop returns failure second time. */
        pContext->appCallback( pContext, &packetInfo, &deserializedInfo );
        status = MQTTRecvFailed;
    }

    return status;
}

/**
 * @brief Function to initialize MQTT Agent Context to valid parameters.
 */
static void setupAgentContext( MQTTAgentContext_t * pAgentContext )
{
    MQTTAgentMessageInterface_t messageInterface = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };
    TransportInterface_t transportInterface = { 0 };
    void * incomingPacketContext = NULL;
    MQTTStatus_t mqttStatus;

    messageInterface.pMsgCtx = &globalMessageContext;
    messageInterface.send = stubSend;
    messageInterface.recv = stubReceive;
    messageInterface.releaseCommand = stubReleaseCommand;
    messageInterface.getCommand = stubGetCommand;

    MQTT_Init_Stub( MQTT_Init_CustomStub );
    MQTT_InitStatefulQoS_ExpectAnyArgsAndReturn( MQTTSuccess );

    mqttStatus = MQTTAgent_Init( pAgentContext,
                                 &messageInterface,
                                 &networkBuffer,
                                 &transportInterface,
                                 stubGetTime,
                                 stubPublishCallback,
                                 incomingPacketContext );

    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );
    /* Set packet ID nonzero to indicate initialization. */
    pAgentContext->mqttContext.nextPacketId = 1U;
}

/**
 * @brief Helper function to test API functions of the form
 * MQTTStatus_t func( MQTTAgentContext_t *, MQTTAgentCommandInfo_t * )
 * for invalid parameters.
 *
 * @param[in] FuncToTest Pointer to function to test.
 * @param[in] pFuncName String of function name to print for error messages.
 */
static void invalidParamsTestFunc( MQTTStatus_t ( * FuncToTest )( const MQTTAgentContext_t *, const MQTTAgentCommandInfo_t * ),
                                   const char * pFuncName )
{
    MQTTAgentContext_t agentContext = { 0 };
    MQTTStatus_t mqttStatus;
    MQTTAgentCommandInfo_t commandInfo = { 0 };

    setupAgentContext( &agentContext );

    /* Test for NULL parameters. */
    mqttStatus = ( FuncToTest ) ( &agentContext, NULL );
    TEST_ASSERT_EQUAL_MESSAGE( MQTTBadParameter, mqttStatus, pFuncName );

    mqttStatus = ( FuncToTest ) ( NULL, &commandInfo );
    TEST_ASSERT_EQUAL_MESSAGE( MQTTBadParameter, mqttStatus, pFuncName );

    /* Various NULL parameters for the agent interface. */
    agentContext.agentInterface.send = NULL;
    mqttStatus = ( FuncToTest ) ( &agentContext, &commandInfo );
    TEST_ASSERT_EQUAL_MESSAGE( MQTTBadParameter, mqttStatus, pFuncName );

    agentContext.agentInterface.send = stubSend;
    agentContext.agentInterface.recv = NULL;
    mqttStatus = ( FuncToTest ) ( &agentContext, &commandInfo );
    TEST_ASSERT_EQUAL_MESSAGE( MQTTBadParameter, mqttStatus, pFuncName );

    agentContext.agentInterface.recv = stubReceive;
    agentContext.agentInterface.getCommand = NULL;
    mqttStatus = ( FuncToTest ) ( &agentContext, &commandInfo );
    TEST_ASSERT_EQUAL_MESSAGE( MQTTBadParameter, mqttStatus, pFuncName );

    agentContext.agentInterface.getCommand = stubGetCommand;
    agentContext.agentInterface.releaseCommand = NULL;
    mqttStatus = ( FuncToTest ) ( &agentContext, &commandInfo );
    TEST_ASSERT_EQUAL_MESSAGE( MQTTBadParameter, mqttStatus, pFuncName );

    agentContext.agentInterface.releaseCommand = stubReleaseCommand;
    agentContext.agentInterface.pMsgCtx = NULL;
    mqttStatus = ( FuncToTest ) ( &agentContext, &commandInfo );
    TEST_ASSERT_EQUAL_MESSAGE( MQTTBadParameter, mqttStatus, pFuncName );

    agentContext.agentInterface.pMsgCtx = &globalMessageContext;
    /* Invalid packet ID to indicate uninitialized context. */
    agentContext.mqttContext.nextPacketId = MQTT_PACKET_ID_INVALID;
    mqttStatus = ( FuncToTest ) ( &agentContext, &commandInfo );
    TEST_ASSERT_EQUAL_MESSAGE( MQTTBadParameter, mqttStatus, pFuncName );
}

/* ========================================================================== */

/**
 * @brief Test that MQTTAgent_Init is able to update the context object correctly.
 */
void test_MQTTAgent_Init_Happy_Path( void )
{
    MQTTAgentContext_t mqttAgentContext;
    MQTTAgentMessageInterface_t msgInterface = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };
    TransportInterface_t transportInterface = { 0 };
    void * incomingPacketContext = NULL;
    MQTTAgentMessageContext_t msg;
    MQTTStatus_t mqttStatus;

    msgInterface.pMsgCtx = &msg;
    msgInterface.send = stubSend;
    msgInterface.recv = stubReceive;
    msgInterface.releaseCommand = stubReleaseCommand;
    msgInterface.getCommand = stubGetCommand;

    MQTT_Init_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_InitStatefulQoS_ExpectAnyArgsAndReturn( MQTTSuccess );

    mqttStatus = MQTTAgent_Init( &mqttAgentContext, &msgInterface, &networkBuffer, &transportInterface, stubGetTime, stubPublishCallback, incomingPacketContext );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );
    TEST_ASSERT_EQUAL_PTR( stubPublishCallback, mqttAgentContext.pIncomingCallback );
    TEST_ASSERT_EQUAL_PTR( incomingPacketContext, mqttAgentContext.pIncomingCallbackContext );
    TEST_ASSERT_EQUAL_MEMORY( &msgInterface, &mqttAgentContext.agentInterface, sizeof( msgInterface ) );
}

/**
 * @brief Test that MQTTAgent_Init is able to update the context object correctly.
 */
void test_MQTTAgent_Init_BadParameter1( void )
{
    MQTTAgentContext_t mqttAgentContext;
    MQTTAgentMessageInterface_t msgInterface = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };
    TransportInterface_t transportInterface = { 0 };
    void * incomingPacketContext = NULL;
    MQTTAgentMessageContext_t msg;
    MQTTStatus_t mqttStatus;

    msgInterface.pMsgCtx = &msg;
    msgInterface.send = stubSend;
    msgInterface.recv = stubReceive;
    msgInterface.releaseCommand = stubReleaseCommand;
    msgInterface.getCommand = stubGetCommand;

    MQTT_Init_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTT_InitStatefulQoS_ExpectAnyArgsAndReturn( MQTTBadParameter );

    mqttStatus = MQTTAgent_Init( &mqttAgentContext, &msgInterface, &networkBuffer, &transportInterface, stubGetTime, stubPublishCallback, incomingPacketContext );
    TEST_ASSERT_EQUAL( MQTTBadParameter, mqttStatus );
}

/**
 * @brief Test that MQTTAgent_Init fails due to bad parameter.
 */
void test_MQTTAgent_Init_BadParameter2( void )
{
    MQTTAgentContext_t mqttAgentContext;
    MQTTAgentMessageInterface_t msgInterface = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };
    TransportInterface_t transportInterface = { 0 };
    void * incomingPacketContext = NULL;
    MQTTAgentMessageContext_t msg;
    MQTTStatus_t mqttStatus;

    msgInterface.pMsgCtx = &msg;
    msgInterface.send = stubSend;
    msgInterface.recv = stubReceive;
    msgInterface.releaseCommand = stubReleaseCommand;
    msgInterface.getCommand = stubGetCommand;

    MQTT_Init_ExpectAnyArgsAndReturn( MQTTBadParameter );

    mqttStatus = MQTTAgent_Init( &mqttAgentContext, &msgInterface, &networkBuffer, &transportInterface, stubGetTime, stubPublishCallback, incomingPacketContext );
    TEST_ASSERT_EQUAL( MQTTBadParameter, mqttStatus );
}

/**
 * @brief Test that any NULL parameter causes MQTTAgent_Init to return MQTTBadParameter.
 */
void test_MQTTAgent_Init_Invalid_Params( void )
{
    MQTTAgentContext_t mqttAgentContext;
    MQTTAgentMessageInterface_t msgInterface = { 0 };
    MQTTFixedBuffer_t networkBuffer = { 0 };
    TransportInterface_t transportInterface = { 0 };
    MQTTAgentIncomingPublishCallback_t incomingCallback = stubPublishCallback;
    void * incomingPacketContext = NULL;
    MQTTAgentMessageContext_t msg;
    MQTTStatus_t mqttStatus;

    msgInterface.pMsgCtx = &msg;
    msgInterface.send = stubSend;
    msgInterface.recv = stubReceive;
    msgInterface.getCommand = stubGetCommand;
    msgInterface.releaseCommand = stubReleaseCommand;

    /* Check that MQTTBadParameter is returned if any NULL parameters are passed. */
    mqttStatus = MQTTAgent_Init( NULL, &msgInterface, &networkBuffer, &transportInterface, stubGetTime, incomingCallback, incomingPacketContext );
    TEST_ASSERT_EQUAL( MQTTBadParameter, mqttStatus );

    mqttStatus = MQTTAgent_Init( &mqttAgentContext, NULL, &networkBuffer, &transportInterface, stubGetTime, incomingCallback, incomingPacketContext );
    TEST_ASSERT_EQUAL( MQTTBadParameter, mqttStatus );

    mqttStatus = MQTTAgent_Init( &mqttAgentContext, &msgInterface, &networkBuffer, NULL, stubGetTime, incomingCallback, incomingPacketContext );
    TEST_ASSERT_EQUAL( MQTTBadParameter, mqttStatus );

    /* Test if NULL is passed for any of the function pointers. */
    mqttStatus = MQTTAgent_Init( &mqttAgentContext, &msgInterface, &networkBuffer, &transportInterface, stubGetTime, NULL, incomingPacketContext );
    TEST_ASSERT_EQUAL( MQTTBadParameter, mqttStatus );

    mqttStatus = MQTTAgent_Init( &mqttAgentContext, &msgInterface, &networkBuffer, &transportInterface, NULL, incomingCallback, incomingPacketContext );
    TEST_ASSERT_EQUAL( MQTTBadParameter, mqttStatus );

    msgInterface.pMsgCtx = NULL;
    mqttStatus = MQTTAgent_Init( &mqttAgentContext, &msgInterface, &networkBuffer, &transportInterface, stubGetTime, incomingCallback, incomingPacketContext );
    TEST_ASSERT_EQUAL( MQTTBadParameter, mqttStatus );

    msgInterface.pMsgCtx = &msg;
    msgInterface.send = NULL;
    mqttStatus = MQTTAgent_Init( &mqttAgentContext, &msgInterface, &networkBuffer, &transportInterface, stubGetTime, incomingCallback, incomingPacketContext );
    TEST_ASSERT_EQUAL( MQTTBadParameter, mqttStatus );

    msgInterface.send = stubSend;
    msgInterface.recv = NULL;
    mqttStatus = MQTTAgent_Init( &mqttAgentContext, &msgInterface, &networkBuffer, &transportInterface, stubGetTime, incomingCallback, incomingPacketContext );
    TEST_ASSERT_EQUAL( MQTTBadParameter, mqttStatus );

    msgInterface.recv = stubReceive;
    msgInterface.releaseCommand = NULL;
    mqttStatus = MQTTAgent_Init( &mqttAgentContext, &msgInterface, &networkBuffer, &transportInterface, stubGetTime, incomingCallback, incomingPacketContext );
    TEST_ASSERT_EQUAL( MQTTBadParameter, mqttStatus );

    msgInterface.releaseCommand = stubReleaseCommand;
    msgInterface.getCommand = NULL;
    mqttStatus = MQTTAgent_Init( &mqttAgentContext, &msgInterface, &networkBuffer, &transportInterface, stubGetTime, incomingCallback, incomingPacketContext );
    TEST_ASSERT_EQUAL( MQTTBadParameter, mqttStatus );

    msgInterface.getCommand = stubGetCommand;

    /* MQTT_Init() should check the network buffer. */
    MQTT_Init_ExpectAnyArgsAndReturn( MQTTBadParameter );
    mqttStatus = MQTTAgent_Init( &mqttAgentContext, &msgInterface, NULL, &transportInterface, stubGetTime, incomingCallback, incomingPacketContext );
    TEST_ASSERT_EQUAL( MQTTBadParameter, mqttStatus );
}

/**
 * @brief Test that any NULL parameter causes MQTTAgent_ResumeSession to return MQTTBadParameter.
 */
void test_MQTTAgent_ResumeSession_Invalid_Params( void )
{
    bool sessionPresent = true;
    MQTTStatus_t mqttStatus;

    MQTTAgentContext_t mqttAgentContext;

    setupAgentContext( &mqttAgentContext );

    /* Check that MQTTBadParameter is returned if any NULL mqttAgentContext is passed. */
    mqttStatus = MQTTAgent_ResumeSession( NULL, sessionPresent );
    TEST_ASSERT_EQUAL( MQTTBadParameter, mqttStatus );

    /* Check that MQTTBadParameter is returned if the MQTT context has not been initialized. */
    mqttAgentContext.mqttContext.nextPacketId = 0;
    mqttStatus = MQTTAgent_ResumeSession( &mqttAgentContext, sessionPresent );
    TEST_ASSERT_EQUAL( MQTTBadParameter, mqttStatus );
}


void test_MQTTAgent_ResumeSession_session_present_no_resent_publishes( void )
{
    bool sessionPresent = true;
    MQTTStatus_t mqttStatus;
    MQTTAgentContext_t mqttAgentContext;

    setupAgentContext( &mqttAgentContext );

    MQTT_PublishToResend_IgnoreAndReturn( MQTT_PACKET_ID_INVALID );
    mqttStatus = MQTTAgent_ResumeSession( &mqttAgentContext, sessionPresent );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );
}

void test_MQTTAgent_ResumeSession_session_present_no_publish_found( void )
{
    bool sessionPresent = true;
    MQTTStatus_t mqttStatus;
    MQTTAgentContext_t mqttAgentContext;
    MQTTAgentCommand_t command = { 0 };

    setupAgentContext( &mqttAgentContext );

    MQTT_PublishToResend_ExpectAnyArgsAndReturn( 2 );
    mqttAgentContext.pPendingAcks[ 0 ].packetId = 1U;
    mqttAgentContext.pPendingAcks[ 0 ].pOriginalCommand = &command;

    MQTT_PublishToResend_ExpectAnyArgsAndReturn( MQTT_PACKET_ID_INVALID );
    mqttStatus = MQTTAgent_ResumeSession( &mqttAgentContext, sessionPresent );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );
}

/**
 * @brief Tests that the MQTTAgent_ResumeSession API clears the entries in pending
 * acknowledgments' list only for SUBSCRIBE and UNSUBSCRIBE operations on a session
 * resumption.
 */
void test_MQTTAgent_ResumeSession_session_present_clear_pending_subscribe_unsubscribe( void )
{
    bool sessionPresent = true;
    MQTTStatus_t mqttStatus;
    MQTTAgentContext_t mqttAgentContext;
    MQTTAgentCommand_t publishCommand = { 0 };
    MQTTAgentCommand_t subscribeCommand = { 0 };
    MQTTAgentCommand_t unsubscribeCommand = { 0 };
    const uint16_t pubPacketId = 1U;

    subscribeCommand.commandType = SUBSCRIBE;
    unsubscribeCommand.commandType = UNSUBSCRIBE;
    publishCommand.commandType = PUBLISH;

    setupAgentContext( &mqttAgentContext );

    /* Setup the pending ack list to contain operations for SUBSCRIBE
     * UNSUBSCRIBE and PUBLISH operations. */
    mqttAgentContext.pPendingAcks[ 0 ].packetId = pubPacketId;
    mqttAgentContext.pPendingAcks[ 0 ].pOriginalCommand = &publishCommand;
    mqttAgentContext.pPendingAcks[ 1 ].packetId = pubPacketId + 1;
    mqttAgentContext.pPendingAcks[ 1 ].pOriginalCommand = &subscribeCommand;
    mqttAgentContext.pPendingAcks[ MQTT_AGENT_MAX_OUTSTANDING_ACKS - 1 ].packetId = pubPacketId + 2;
    mqttAgentContext.pPendingAcks[ MQTT_AGENT_MAX_OUTSTANDING_ACKS - 1 ].pOriginalCommand =
        &unsubscribeCommand;

    /* Even though the list has a pending PUBLISH operation, return no packet ID
     * from MQTT_PublishToResend function as the operation of re-sending publish
     * packet is not part of the scope of this test. */
    MQTT_PublishToResend_IgnoreAndReturn( MQTT_PACKET_ID_INVALID );

    /* Call API under test. */
    mqttStatus = MQTTAgent_ResumeSession( &mqttAgentContext, sessionPresent );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );

    /* Ensure that the list entries for SUBSCRIBE and UNSUBSCRIBE operations have
     * been cleared. */
    TEST_ASSERT_EQUAL( MQTT_PACKET_ID_INVALID, mqttAgentContext.pPendingAcks[ 1 ].packetId );
    TEST_ASSERT_EQUAL_PTR( NULL, mqttAgentContext.pPendingAcks[ 1 ].pOriginalCommand );
    TEST_ASSERT_EQUAL( MQTT_PACKET_ID_INVALID, mqttAgentContext.
                          pPendingAcks[ MQTT_AGENT_MAX_OUTSTANDING_ACKS - 1 ].packetId );
    TEST_ASSERT_EQUAL_PTR( NULL, mqttAgentContext.
                              pPendingAcks[ MQTT_AGENT_MAX_OUTSTANDING_ACKS - 1 ].pOriginalCommand );

    /* Ensure that the list entry for PUBLISH operation was not removed. */
    TEST_ASSERT_EQUAL( pubPacketId, mqttAgentContext.pPendingAcks[ 0 ].packetId );
    TEST_ASSERT_EQUAL_PTR( &publishCommand, mqttAgentContext.pPendingAcks[ 0 ].pOriginalCommand );
}

void test_MQTTAgent_ResumeSession_failed_publish( void )
{
    bool sessionPresent = true;
    MQTTStatus_t mqttStatus;
    MQTTAgentContext_t mqttAgentContext;
    MQTTAgentCommand_t command = { 0 };
    MQTTPublishInfo_t args = { 0 };

    setupAgentContext( &mqttAgentContext );

    command.pArgs = &args;
    mqttAgentContext.pPendingAcks[ 0 ].packetId = 1U;
    mqttAgentContext.pPendingAcks[ 0 ].pOriginalCommand = &command;
    /* Check that failed resending publish return MQTTSendFailed. */
    MQTT_PublishToResend_IgnoreAndReturn( 1 );
    MQTT_Publish_IgnoreAndReturn( MQTTSendFailed );
    mqttStatus = MQTTAgent_ResumeSession( &mqttAgentContext, sessionPresent );
    TEST_ASSERT_EQUAL( MQTTSendFailed, mqttStatus );
}

void test_MQTTAgent_ResumeSession_publish_resend_success( void )
{
    bool sessionPresent = true;
    MQTTStatus_t mqttStatus;
    MQTTAgentContext_t mqttAgentContext;
    MQTTAgentCommand_t command = { 0 };
    MQTTPublishInfo_t args = { 0 };
    MQTTAgentAckInfo_t ackInfo;

    setupAgentContext( &mqttAgentContext );

    command.pArgs = &args;

    ackInfo.packetId = 1U;
    ackInfo.pOriginalCommand = &command;
    mqttAgentContext.pPendingAcks[ 0 ] = ackInfo;

    /* Check that publish ack is resent successfully when session resumes. */
    MQTT_PublishToResend_ExpectAnyArgsAndReturn( 1 );
    MQTT_Publish_IgnoreAndReturn( MQTTSuccess );
    MQTT_PublishToResend_ExpectAnyArgsAndReturn( MQTT_PACKET_ID_INVALID );
    mqttStatus = MQTTAgent_ResumeSession( &mqttAgentContext, sessionPresent );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );
}


void test_MQTTAgent_ResumeSession_no_session_present( void )
{
    MQTTStatus_t mqttStatus;
    MQTTAgentContext_t mqttAgentContext;
    MQTTAgentCommand_t command = { 0 };

    setupAgentContext( &mqttAgentContext );

    command.pCommandCompleteCallback = NULL;
    mqttAgentContext.pPendingAcks[ 1 ].packetId = 1U;
    mqttAgentContext.pPendingAcks[ 1 ].pOriginalCommand = &command;
    /* Check that only acknowledgments with valid packet IDs are cleared. */
    mqttStatus = MQTTAgent_ResumeSession( &mqttAgentContext, false );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );
    TEST_ASSERT_EQUAL( 0, mqttAgentContext.pPendingAcks[ 1 ].packetId );
    TEST_ASSERT_EQUAL( NULL, mqttAgentContext.pPendingAcks[ 1 ].pOriginalCommand );

    command.pCommandCompleteCallback = stubCompletionCallback;
    mqttAgentContext.pPendingAcks[ 1 ].packetId = 1U;
    mqttAgentContext.pPendingAcks[ 1 ].pOriginalCommand = &command;
    /* Check that command callback is called if it is specified to indicate network error. */
    mqttStatus = MQTTAgent_ResumeSession( &mqttAgentContext, false );
    TEST_ASSERT_EQUAL_INT( 1, commandCompleteCallbackCount );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );
}

/* ========================================================================== */

/**
 * @brief Test error cases when a command cannot be obtained.
 */
void test_MQTTAgent_Ping_Command_Allocation_Failure( void )
{
    MQTTAgentContext_t agentContext = { 0 };
    MQTTStatus_t mqttStatus;
    MQTTAgentCommandInfo_t commandInfo = { 0 };

    setupAgentContext( &agentContext );

    pCommandToReturn = NULL;
    mqttStatus = MQTTAgent_Ping( &agentContext, &commandInfo );
    TEST_ASSERT_EQUAL( MQTTNoMemory, mqttStatus );
}

/**
 * @brief Test error case when a command cannot be enqueued.
 */
void test_MQTTAgent_Ping_Command_Send_Failure( void )
{
    MQTTAgentContext_t agentContext = { 0 };
    MQTTStatus_t mqttStatus;
    MQTTAgentCommandInfo_t commandInfo = { 0 };
    MQTTAgentCommand_t command = { 0 };

    setupAgentContext( &agentContext );

    pCommandToReturn = &command;
    agentContext.agentInterface.send = stubSendFail;
    mqttStatus = MQTTAgent_Ping( &agentContext, &commandInfo );
    TEST_ASSERT_EQUAL( MQTTSendFailed, mqttStatus );
    /* Test that the command was released. */
    TEST_ASSERT_EQUAL_INT( 1, commandReleaseCallCount );
    /* Also test that the command was set. */
    TEST_ASSERT_EQUAL( PING, command.commandType );
}

/**
 * @brief Test that an MQTTNoMemory error is returned when there
 * is no more space to store a pending acknowledgment for
 * a command that expects one.
 */
void test_MQTTAgent_Subscribe_No_Ack_Space( void )
{
    MQTTAgentContext_t agentContext;
    MQTTStatus_t mqttStatus;
    MQTTAgentCommandInfo_t commandInfo = { 0 };
    MQTTAgentCommand_t command = { 0 };
    MQTTSubscribeInfo_t subscribeInfo = { 0 };
    MQTTAgentSubscribeArgs_t subscribeArgs = { 0 };
    size_t i;

    setupAgentContext( &agentContext );
    pCommandToReturn = &command;

    /* No space in pending ack list. */
    for( i = 0; i < MQTT_AGENT_MAX_OUTSTANDING_ACKS; i++ )
    {
        agentContext.pPendingAcks[ i ].packetId = ( i + 1 );
    }

    subscribeArgs.pSubscribeInfo = &subscribeInfo;
    subscribeArgs.numSubscriptions = 1U;
    mqttStatus = MQTTAgent_Subscribe( &agentContext, &subscribeArgs, &commandInfo );
    TEST_ASSERT_EQUAL( MQTTNoMemory, mqttStatus );
}

/**
 * @brief Test MQTTAgent_Subscribe() with invalid parameters.
 */
void test_MQTTAgent_Subscribe_Invalid_Parameters( void )
{
    MQTTAgentContext_t agentContext;
    MQTTStatus_t mqttStatus;
    MQTTAgentCommandInfo_t commandInfo = { 0 };
    MQTTAgentCommand_t command = { 0 };
    MQTTSubscribeInfo_t subscribeInfo = { 0 };
    MQTTAgentSubscribeArgs_t subscribeArgs = { 0 };

    setupAgentContext( &agentContext );
    pCommandToReturn = &command;

    /* NULL parameters. */
    mqttStatus = MQTTAgent_Subscribe( NULL, &subscribeArgs, &commandInfo );
    TEST_ASSERT_EQUAL( MQTTBadParameter, mqttStatus );

    mqttStatus = MQTTAgent_Subscribe( &agentContext, NULL, &commandInfo );
    TEST_ASSERT_EQUAL( MQTTBadParameter, mqttStatus );

    mqttStatus = MQTTAgent_Subscribe( &agentContext, &subscribeArgs, NULL );
    TEST_ASSERT_EQUAL( MQTTBadParameter, mqttStatus );

    /* Incorrect subscribe args. */
    mqttStatus = MQTTAgent_Subscribe( &agentContext, &subscribeArgs, &commandInfo );
    TEST_ASSERT_EQUAL( MQTTBadParameter, mqttStatus );

    subscribeArgs.pSubscribeInfo = &subscribeInfo;
    subscribeArgs.numSubscriptions = 0U;
    mqttStatus = MQTTAgent_Subscribe( &agentContext, &subscribeArgs, &commandInfo );
    TEST_ASSERT_EQUAL( MQTTBadParameter, mqttStatus );
}

/**
 * @brief Test that MQTTAgent_Subscribe() works as intended.
 */
void test_MQTTAgent_Subscribe_success( void )
{
    MQTTAgentContext_t agentContext;
    MQTTStatus_t mqttStatus;
    MQTTAgentCommandInfo_t commandInfo = { 0 };
    MQTTAgentCommand_t command = { 0 };
    MQTTSubscribeInfo_t subscribeInfo = { 0 };
    MQTTAgentSubscribeArgs_t subscribeArgs = { 0 };

    setupAgentContext( &agentContext );
    pCommandToReturn = &command;

    /* Success case. */
    subscribeArgs.pSubscribeInfo = &subscribeInfo;
    subscribeArgs.numSubscriptions = 1U;
    mqttStatus = MQTTAgent_Subscribe( &agentContext, &subscribeArgs, &commandInfo );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );
    TEST_ASSERT_EQUAL_PTR( &command, globalMessageContext.pSentCommand );
    TEST_ASSERT_EQUAL( SUBSCRIBE, command.commandType );
    TEST_ASSERT_EQUAL_PTR( &subscribeArgs, command.pArgs );
    TEST_ASSERT_NULL( command.pCommandCompleteCallback );
}

/**
 * @brief Test MQTTAgent_Unsubscribe() with invalid parameters.
 */
void test_MQTTAgent_Unsubscribe_Invalid_Parameters( void )
{
    MQTTAgentContext_t agentContext;
    MQTTStatus_t mqttStatus;
    MQTTAgentCommandInfo_t commandInfo = { 0 };
    MQTTAgentCommand_t command = { 0 };
    MQTTSubscribeInfo_t subscribeInfo = { 0 };
    MQTTAgentSubscribeArgs_t subscribeArgs = { 0 };

    setupAgentContext( &agentContext );
    pCommandToReturn = &command;

    /* NULL parameters. */
    mqttStatus = MQTTAgent_Unsubscribe( NULL, &subscribeArgs, &commandInfo );
    TEST_ASSERT_EQUAL( MQTTBadParameter, mqttStatus );

    mqttStatus = MQTTAgent_Unsubscribe( &agentContext, NULL, &commandInfo );
    TEST_ASSERT_EQUAL( MQTTBadParameter, mqttStatus );

    mqttStatus = MQTTAgent_Unsubscribe( &agentContext, &subscribeArgs, NULL );
    TEST_ASSERT_EQUAL( MQTTBadParameter, mqttStatus );

    /* Incorrect subscribe args. */
    mqttStatus = MQTTAgent_Unsubscribe( &agentContext, &subscribeArgs, &commandInfo );
    TEST_ASSERT_EQUAL( MQTTBadParameter, mqttStatus );

    subscribeArgs.pSubscribeInfo = &subscribeInfo;
    subscribeArgs.numSubscriptions = 0U;
    mqttStatus = MQTTAgent_Unsubscribe( &agentContext, &subscribeArgs, &commandInfo );
    TEST_ASSERT_EQUAL( MQTTBadParameter, mqttStatus );
}

/**
 * @brief Test that MQTTAgent_Unsubscribe() works as intended.
 */
void test_MQTTAgent_Unsubscribe_success( void )
{
    MQTTAgentContext_t agentContext;
    MQTTStatus_t mqttStatus;
    MQTTAgentCommandInfo_t commandInfo = { 0 };
    MQTTAgentCommand_t command = { 0 };
    MQTTSubscribeInfo_t subscribeInfo = { 0 };
    MQTTAgentSubscribeArgs_t subscribeArgs = { 0 };

    setupAgentContext( &agentContext );
    pCommandToReturn = &command;
    commandInfo.cmdCompleteCallback = stubCompletionCallback;

    /* Success case. */
    subscribeArgs.pSubscribeInfo = &subscribeInfo;
    subscribeArgs.numSubscriptions = 1U;
    mqttStatus = MQTTAgent_Unsubscribe( &agentContext, &subscribeArgs, &commandInfo );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );
    TEST_ASSERT_EQUAL_PTR( &command, globalMessageContext.pSentCommand );
    TEST_ASSERT_EQUAL( UNSUBSCRIBE, command.commandType );
    TEST_ASSERT_EQUAL_PTR( &subscribeArgs, command.pArgs );
    TEST_ASSERT_EQUAL_PTR( stubCompletionCallback, command.pCommandCompleteCallback );
}

/* ========================================================================== */

/**
 * @brief Test MQTTAgent_Publish() with invalid parameters.
 */
void test_MQTTAgent_Publish_Invalid_Parameters( void )
{
    MQTTAgentContext_t agentContext = { 0 };
    MQTTStatus_t mqttStatus;
    MQTTAgentCommandInfo_t commandInfo = { 0 };
    MQTTAgentCommand_t command = { 0 };
    MQTTPublishInfo_t publishInfo = { 0 };

    setupAgentContext( &agentContext );
    pCommandToReturn = &command;
    commandInfo.cmdCompleteCallback = stubCompletionCallback;
    /* Test topic name. */
    publishInfo.pTopicName = "test";
    publishInfo.topicNameLength = 4;

    /* NULL parameters. */
    mqttStatus = MQTTAgent_Publish( NULL, &publishInfo, &commandInfo );
    TEST_ASSERT_EQUAL( MQTTBadParameter, mqttStatus );

    mqttStatus = MQTTAgent_Publish( &agentContext, NULL, &commandInfo );
    TEST_ASSERT_EQUAL( MQTTBadParameter, mqttStatus );

    mqttStatus = MQTTAgent_Publish( &agentContext, &publishInfo, NULL );
    TEST_ASSERT_EQUAL( MQTTBadParameter, mqttStatus );

    /* This needs to be large enough to hold the PUBLISH:
     * 1 byte: control header
     * 1 byte: remaining length
     * 2 bytes: topic name length
     * 1+ bytes: topic name.
     * For this test case, the buffer must have size at least
     * 1+1+2+4=8. */
    agentContext.mqttContext.networkBuffer.size = 6;
    mqttStatus = MQTTAgent_Publish( &agentContext, &publishInfo, &commandInfo );
    TEST_ASSERT_EQUAL( MQTTBadParameter, mqttStatus );
}

/**
 * @brief Test that an MQTTNoMemory error is returned when there
 * is no more space to store a pending acknowledgment for
 * a command that expects one.
 */
void test_MQTTAgent_Publish_No_Ack_Space( void )
{
    MQTTAgentContext_t agentContext = { 0 };
    MQTTStatus_t mqttStatus;
    MQTTAgentCommandInfo_t commandInfo = { 0 };
    MQTTAgentCommand_t command = { 0 };
    MQTTPublishInfo_t publishInfo = { 0 };
    size_t i;

    setupAgentContext( &agentContext );
    pCommandToReturn = &command;
    commandInfo.cmdCompleteCallback = stubCompletionCallback;
    /* Test topic name. */
    publishInfo.pTopicName = "test";
    publishInfo.topicNameLength = 4;
    /* Ack space is only necessary for QoS > 0. */
    publishInfo.qos = MQTTQoS1;

    /* No space in pending ack list. */
    for( i = 0; i < MQTT_AGENT_MAX_OUTSTANDING_ACKS; i++ )
    {
        agentContext.pPendingAcks[ i ].packetId = ( i + 1 );
    }

    /* This needs to be large enough to hold the PUBLISH:
     * 1 byte: control header
     * 1 byte: remaining length
     * 2 bytes: topic name length
     * 1+ bytes: topic name.
     * For this test case, the buffer must have size at least
     * 1+1+2+4=8. */
    agentContext.mqttContext.networkBuffer.size = 10;
    mqttStatus = MQTTAgent_Publish( &agentContext, &publishInfo, &commandInfo );
    TEST_ASSERT_EQUAL( MQTTNoMemory, mqttStatus );
}

/**
 * @brief Test that MQTTAgent_Publish() works as intended.
 */
void test_MQTTAgent_Publish_success( void )
{
    MQTTAgentContext_t agentContext = { 0 };
    MQTTStatus_t mqttStatus;
    MQTTAgentCommandInfo_t commandInfo = { 0 };
    MQTTAgentCommand_t command = { 0 };
    MQTTPublishInfo_t publishInfo = { 0 };

    setupAgentContext( &agentContext );
    pCommandToReturn = &command;
    commandInfo.cmdCompleteCallback = stubCompletionCallback;
    /* Test topic name. */
    publishInfo.pTopicName = "test";
    publishInfo.topicNameLength = 4;

    /* This needs to be large enough to hold the PUBLISH:
     * 1 byte: control header
     * 1 byte: remaining length
     * 2 bytes: topic name length
     * 1+ bytes: topic name.
     * For this test case, the buffer must have size at least
     * 1+1+2+4=8. */
    agentContext.mqttContext.networkBuffer.size = 10;
    mqttStatus = MQTTAgent_Publish( &agentContext, &publishInfo, &commandInfo );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );
    TEST_ASSERT_EQUAL_PTR( &command, globalMessageContext.pSentCommand );
    TEST_ASSERT_EQUAL( PUBLISH, command.commandType );
    TEST_ASSERT_EQUAL_PTR( &publishInfo, command.pArgs );
    TEST_ASSERT_EQUAL_PTR( stubCompletionCallback, command.pCommandCompleteCallback );
}

/* ========================================================================== */

/**
 * @brief Test MQTTAgent_Connect() with invalid parameters.
 */
void test_MQTTAgent_Connect_Invalid_Parameters( void )
{
    MQTTAgentContext_t agentContext = { 0 };
    MQTTStatus_t mqttStatus;
    MQTTAgentCommandInfo_t commandInfo = { 0 };
    MQTTAgentCommand_t command = { 0 };
    MQTTAgentConnectArgs_t connectArgs = { 0 };
    MQTTConnectInfo_t connectInfo = { 0 };

    setupAgentContext( &agentContext );
    pCommandToReturn = &command;
    commandInfo.cmdCompleteCallback = stubCompletionCallback;
    connectArgs.pConnectInfo = &connectInfo;

    /* NULL parameters. */
    mqttStatus = MQTTAgent_Connect( NULL, &connectArgs, &commandInfo );
    TEST_ASSERT_EQUAL( MQTTBadParameter, mqttStatus );

    mqttStatus = MQTTAgent_Connect( &agentContext, NULL, &commandInfo );
    TEST_ASSERT_EQUAL( MQTTBadParameter, mqttStatus );

    mqttStatus = MQTTAgent_Connect( &agentContext, &connectArgs, NULL );
    TEST_ASSERT_EQUAL( MQTTBadParameter, mqttStatus );

    /* Invalid argument. */
    connectArgs.pConnectInfo = NULL;
    mqttStatus = MQTTAgent_Connect( &agentContext, &connectArgs, &commandInfo );
    TEST_ASSERT_EQUAL( MQTTBadParameter, mqttStatus );
}

/**
 * @brief Test that MQTTAgent_Connect() works as intended.
 */
void test_MQTTAgent_Connect_success( void )
{
    MQTTAgentContext_t agentContext;
    MQTTStatus_t mqttStatus;
    MQTTAgentCommandInfo_t commandInfo = { 0 };
    MQTTAgentCommand_t command = { 0 };
    MQTTAgentConnectArgs_t connectArgs = { 0 };
    MQTTConnectInfo_t connectInfo = { 0 };

    setupAgentContext( &agentContext );
    pCommandToReturn = &command;
    commandInfo.cmdCompleteCallback = stubCompletionCallback;

    /* Success case. */
    connectArgs.pConnectInfo = &connectInfo;
    mqttStatus = MQTTAgent_Connect( &agentContext, &connectArgs, &commandInfo );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );
    TEST_ASSERT_EQUAL_PTR( &command, globalMessageContext.pSentCommand );
    TEST_ASSERT_EQUAL( CONNECT, command.commandType );
    TEST_ASSERT_EQUAL_PTR( &connectArgs, command.pArgs );
    TEST_ASSERT_EQUAL_PTR( stubCompletionCallback, command.pCommandCompleteCallback );
}

/* ========================================================================== */

/**
 * @brief Test MQTTAgent_ProcessLoop() with invalid parameters.
 */
void test_MQTTAgent_ProcessLoop_Invalid_Params( void )
{
    /* Call the common helper function with the function pointer and name. */
    invalidParamsTestFunc( MQTTAgent_ProcessLoop, "Function=MQTTAgent_ProcessLoop" );
}

/**
 * @brief Test that MQTTAgent_ProcessLoop() works as intended.
 */
void test_MQTTAgent_ProcessLoop_success( void )
{
    MQTTAgentContext_t agentContext;
    MQTTStatus_t mqttStatus;
    MQTTAgentCommandInfo_t commandInfo = { 0 };
    MQTTAgentCommand_t command = { 0 };

    setupAgentContext( &agentContext );
    pCommandToReturn = &command;

    /* Success case. */
    mqttStatus = MQTTAgent_ProcessLoop( &agentContext, &commandInfo );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );
    TEST_ASSERT_EQUAL_PTR( &command, globalMessageContext.pSentCommand );
    TEST_ASSERT_EQUAL( PROCESSLOOP, command.commandType );
    TEST_ASSERT_NULL( command.pArgs );
    TEST_ASSERT_NULL( command.pCommandCompleteCallback );
}

/* ========================================================================== */

/**
 * @brief Test MQTTAgent_Disconnect() with invalid parameters.
 */
void test_MQTTAgent_Disconnect_Invalid_Params( void )
{
    /* Call the common helper function with the function pointer and name. */
    invalidParamsTestFunc( MQTTAgent_Disconnect, "Function=MQTTAgent_Disconnect" );
}

/**
 * @brief Test that MQTTAgent_Disconnect() works as intended.
 */
void test_MQTTAgent_Disconnect_success( void )
{
    MQTTAgentContext_t agentContext;
    MQTTStatus_t mqttStatus;
    MQTTAgentCommandInfo_t commandInfo = { 0 };
    MQTTAgentCommand_t command = { 0 };

    setupAgentContext( &agentContext );
    pCommandToReturn = &command;
    commandInfo.cmdCompleteCallback = stubCompletionCallback;

    /* Success case. */
    mqttStatus = MQTTAgent_Disconnect( &agentContext, &commandInfo );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );
    TEST_ASSERT_EQUAL_PTR( &command, globalMessageContext.pSentCommand );
    TEST_ASSERT_EQUAL( DISCONNECT, command.commandType );
    TEST_ASSERT_NULL( command.pArgs );
    TEST_ASSERT_EQUAL_PTR( stubCompletionCallback, command.pCommandCompleteCallback );
}

/* ========================================================================== */

/**
 * @brief Test MQTTAgent_Disconnect() with invalid parameters.
 */
void test_MQTTAgent_Ping_Invalid_Params( void )
{
    /* Call the common helper function with the function pointer and name. */
    invalidParamsTestFunc( MQTTAgent_Ping, "Function=MQTTAgent_Ping" );
}

/**
 * @brief Test that MQTTAgent_Ping() works as intended.
 */
void test_MQTTAgent_Ping_success( void )
{
    MQTTAgentContext_t agentContext;
    MQTTStatus_t mqttStatus;
    MQTTAgentCommandInfo_t commandInfo = { 0 };
    MQTTAgentCommand_t command = { 0 };

    setupAgentContext( &agentContext );
    pCommandToReturn = &command;
    commandInfo.cmdCompleteCallback = stubCompletionCallback;

    /* Success case. */
    mqttStatus = MQTTAgent_Ping( &agentContext, &commandInfo );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );
    TEST_ASSERT_EQUAL_PTR( &command, globalMessageContext.pSentCommand );
    TEST_ASSERT_EQUAL( PING, command.commandType );
    TEST_ASSERT_NULL( command.pArgs );
    TEST_ASSERT_EQUAL_PTR( stubCompletionCallback, command.pCommandCompleteCallback );
}

/* ========================================================================== */

/**
 * @brief Test MQTTAgent_Terminate() with invalid parameters.
 */
void test_MQTTAgent_Terminate_Invalid_Params( void )
{
    /* Call the common helper function with the function pointer and name. */
    invalidParamsTestFunc( MQTTAgent_Terminate, "Function=MQTTAgent_Terminate" );
}

/**
 * @brief Test that MQTTAgent_Terminate() works as intended.
 */
void test_MQTTAgent_Terminate_success( void )
{
    MQTTAgentContext_t agentContext;
    MQTTStatus_t mqttStatus;
    MQTTAgentCommandInfo_t commandInfo = { 0 };
    MQTTAgentCommand_t command = { 0 };

    setupAgentContext( &agentContext );
    pCommandToReturn = &command;
    commandInfo.cmdCompleteCallback = stubCompletionCallback;

    /* Success case. */
    mqttStatus = MQTTAgent_Terminate( &agentContext, &commandInfo );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );
    TEST_ASSERT_EQUAL_PTR( &command, globalMessageContext.pSentCommand );
    TEST_ASSERT_EQUAL( TERMINATE, command.commandType );
    TEST_ASSERT_NULL( command.pArgs );
    TEST_ASSERT_EQUAL_PTR( stubCompletionCallback, command.pCommandCompleteCallback );
}

/**
 * @brief Test MQTTAgent_CommandLoop behavior with invalid params.
 */
void test_MQTTAgent_CommandLoop_invalid_params( void )
{
    MQTTStatus_t mqttStatus;
    MQTTAgentContext_t mqttAgentContext;

    mqttStatus = MQTTAgent_CommandLoop( NULL );
    TEST_ASSERT_EQUAL( MQTTBadParameter, mqttStatus );

    setupAgentContext( &mqttAgentContext );

    mqttAgentContext.agentInterface.pMsgCtx = NULL;

    mqttStatus = MQTTAgent_CommandLoop( &mqttAgentContext );
    TEST_ASSERT_EQUAL( MQTTBadParameter, mqttStatus );
}

/**
 * @brief Test MQTTAgent_CommandLoop behavior when there is no command in the command Queue.
 */
void test_MQTTAgent_CommandLoop_with_empty_command_queue( void )
{
    MQTTStatus_t mqttStatus;
    MQTTAgentContext_t mqttAgentContext;

    setupAgentContext( &mqttAgentContext );

    mqttAgentContext.mqttContext.connectStatus = MQTTNotConnected;
    returnFlags.addAcknowledgment = false;
    returnFlags.runProcessLoop = true;
    returnFlags.endLoop = true;

    MQTTAgentCommand_ProcessLoop_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTTAgentCommand_ProcessLoop_ReturnThruPtr_pReturnFlags( &returnFlags );

    mqttStatus = MQTTAgent_CommandLoop( &mqttAgentContext );

    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );
}

/**
 * @brief Test MQTTAgent_CommandLoop behavior when there is command to be processed in the command queue.
 */
void test_MQTTAgent_CommandLoop_process_commands_in_command_queue( void )
{
    MQTTStatus_t mqttStatus;
    MQTTAgentContext_t mqttAgentContext;
    MQTTAgentCommand_t commandToSend = { 0 };

    setupAgentContext( &mqttAgentContext );
    mqttAgentContext.mqttContext.connectStatus = MQTTConnected;
    returnFlags.addAcknowledgment = false;
    returnFlags.runProcessLoop = true;
    returnFlags.endLoop = true;

    MQTTAgentCommand_Publish_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTTAgentCommand_Publish_ReturnThruPtr_pReturnFlags( &returnFlags );
    MQTT_ProcessLoop_IgnoreAndReturn( MQTTSuccess );

    /* Initializing command to be sent to the commandLoop. */
    commandToSend.commandType = PUBLISH;
    commandToSend.pCommandCompleteCallback = stubCompletionCallback;
    commandToSend.pCmdContext = NULL;
    commandToSend.pArgs = NULL;
    mqttAgentContext.agentInterface.pMsgCtx->pSentCommand = &commandToSend;

    mqttStatus = MQTTAgent_CommandLoop( &mqttAgentContext );

    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );
    /* Ensure that callback is invoked. */
    TEST_ASSERT_EQUAL( 1, commandCompleteCallbackCount );

    /* Test case when processing a particular command fails. */
    MQTTAgentCommand_Publish_ExpectAnyArgsAndReturn( MQTTBadParameter );
    MQTTAgentCommand_Publish_ReturnThruPtr_pReturnFlags( &returnFlags );

    mqttStatus = MQTTAgent_CommandLoop( &mqttAgentContext );

    TEST_ASSERT_EQUAL( MQTTBadParameter, mqttStatus );
    TEST_ASSERT_EQUAL( 2, commandCompleteCallbackCount );
}

/**
 * @brief Test that MQTTAgent_CommandLoop adds acknowledgment in pendingAcks for the commands requiring
 * acknowledgments.
 */
void test_MQTTAgent_CommandLoop_add_acknowledgment_success( void )
{
    MQTTStatus_t mqttStatus;
    MQTTAgentContext_t mqttAgentContext;
    MQTTAgentCommand_t commandToSend = { 0 };

    setupAgentContext( &mqttAgentContext );
    mqttAgentContext.mqttContext.connectStatus = MQTTConnected;
    returnFlags.addAcknowledgment = true;
    returnFlags.runProcessLoop = false;
    returnFlags.endLoop = true;
    returnFlags.packetId = 1U;

    MQTTAgentCommand_Publish_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTTAgentCommand_Publish_ReturnThruPtr_pReturnFlags( &returnFlags );

    /* Initializing command to be sent to the commandLoop. */
    commandToSend.commandType = PUBLISH;
    commandToSend.pCommandCompleteCallback = stubCompletionCallback;
    commandToSend.pCmdContext = NULL;
    commandToSend.pArgs = NULL;

    mqttAgentContext.agentInterface.pMsgCtx->pSentCommand = &commandToSend;
    mqttStatus = MQTTAgent_CommandLoop( &mqttAgentContext );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );

    /* Ensure that acknowledgment is added. */
    TEST_ASSERT_EQUAL( 1, mqttAgentContext.pPendingAcks[ 0 ].packetId );
    TEST_ASSERT_EQUAL_PTR( &commandToSend, mqttAgentContext.pPendingAcks[ 0 ].pOriginalCommand );
    /* Ensure that callback is not invoked. */
    TEST_ASSERT_EQUAL( 0, commandCompleteCallbackCount );
}

/**
 * @brief Test that MQTTAgent_CommandLoop returns failure if an operation's entry
 * cannot be added in the list of pending acknowledgments, either due to the array
 * being full OR there being an existing entry for the same packet ID.
 */
void test_MQTTAgent_CommandLoop_add_acknowledgment_failure( void )
{
    MQTTStatus_t mqttStatus;
    MQTTAgentContext_t mqttAgentContext;
    size_t i = 0;
    MQTTAgentCommand_t commandToSend = { 0 };
    const uint16_t testPacketId = 1U;

    setupAgentContext( &mqttAgentContext );
    mqttAgentContext.mqttContext.connectStatus = MQTTConnected;
    returnFlags.addAcknowledgment = true;
    returnFlags.runProcessLoop = false;
    returnFlags.endLoop = false;
    returnFlags.packetId = testPacketId;

    MQTTAgentCommand_Publish_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTTAgentCommand_Publish_ReturnThruPtr_pReturnFlags( &returnFlags );
    MQTT_ProcessLoop_IgnoreAndReturn( MQTTSuccess );

    /* Initializing command to be sent to the commandLoop. */
    commandToSend.commandType = PUBLISH;
    commandToSend.pCommandCompleteCallback = stubCompletionCallback;
    commandToSend.pCmdContext = NULL;
    commandToSend.pArgs = NULL;

    globalMessageContext.pSentCommand = &commandToSend;

    /*** Test case when the list is full and there exists no entry with same packet ID. ***/

    /* Test case when the list of pending acknowledgements is full. */
    for( i = 0; i < MQTT_AGENT_MAX_OUTSTANDING_ACKS; i++ )
    {
        /* Assigning valid packet ID to all array spaces to make no space for incoming acknowledgment. */
        mqttAgentContext.pPendingAcks[ i ].packetId = testPacketId + i + 1;
    }

    /* Call API under test. */
    mqttStatus = MQTTAgent_CommandLoop( &mqttAgentContext );
    TEST_ASSERT_EQUAL( MQTTNoMemory, mqttStatus );

    /* Ensure that callback is invoked. */
    TEST_ASSERT_EQUAL( 1, commandCompleteCallbackCount );

    /***** Test case when list is not full but the operation's packet ID already exists in list. ******/

    /* Reset the completed callback counter. */
    commandCompleteCallbackCount = 0;

    MQTTAgentCommand_Publish_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTTAgentCommand_Publish_ReturnThruPtr_pReturnFlags( &returnFlags );

    /* Test case when there is space availability in pending acks list but
     * there also exists an entry for the same packet ID being attempted to be
     * added. */
    mqttAgentContext.pPendingAcks[ 0 ].packetId = MQTT_PACKET_ID_INVALID;
    mqttAgentContext.pPendingAcks[ 1 ].packetId = returnFlags.packetId;

    /* Call API under test. */
    mqttStatus = MQTTAgent_CommandLoop( &mqttAgentContext );
    TEST_ASSERT_EQUAL( MQTTStateCollision, mqttStatus );

    /* Ensure that callback is invoked. */
    TEST_ASSERT_EQUAL( 1, commandCompleteCallbackCount );
}

/**
 * @brief Test that MQTTAgent_CommandLoop does not add acknowledgments for invalid
 * packet IDs.
 */
void test_MQTTAgent_CommandLoop_add_acknowledgment_invalid_id( void )
{
    MQTTStatus_t mqttStatus;
    MQTTAgentContext_t agentContext;
    MQTTAgentCommand_t command = { 0 };
    MQTTAgentAckInfo_t emptyAck = { 0 };

    setupAgentContext( &agentContext );
    agentContext.mqttContext.connectStatus = MQTTConnected;
    returnFlags.addAcknowledgment = true;
    returnFlags.runProcessLoop = false;
    returnFlags.endLoop = true;
    returnFlags.packetId = 0U;

    MQTTAgentCommand_Publish_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTTAgentCommand_Publish_ReturnThruPtr_pReturnFlags( &returnFlags );

    /* Initializing command to be sent to the commandLoop. */
    command.commandType = PUBLISH;
    command.pCommandCompleteCallback = stubCompletionCallback;
    command.pCmdContext = NULL;
    command.pArgs = NULL;

    globalMessageContext.pSentCommand = &command;
    mqttStatus = MQTTAgent_CommandLoop( &agentContext );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );

    /* Ensure that acknowledgment is not added. */
    TEST_ASSERT_EACH_EQUAL_MEMORY( &emptyAck,
                                   agentContext.pPendingAcks,
                                   sizeof( MQTTAgentAckInfo_t ),
                                   MQTT_AGENT_MAX_OUTSTANDING_ACKS );
    /* Ensure that callback is invoked. */
    TEST_ASSERT_EQUAL( 1, commandCompleteCallbackCount );
}

/**
 * @brief Test mqttEventCallback invocation via MQTT_ProcessLoop.
 * TODO: Split this function up.
 */
void test_MQTTAgent_CommandLoop_with_eventCallback( void )
{
    MQTTStatus_t mqttStatus;
    MQTTAgentContext_t mqttAgentContext;
    MQTTAgentCommand_t command = { 0 }, commandToSend = { 0 };

    /* Setting up MQTT Agent Context. */
    setupAgentContext( &mqttAgentContext );

    mqttAgentContext.mqttContext.connectStatus = MQTTConnected;
    returnFlags.addAcknowledgment = false;
    returnFlags.runProcessLoop = true;
    returnFlags.endLoop = true;

    /* Initializing command to be sent to the commandLoop. */
    commandToSend.commandType = PUBLISH;
    commandToSend.pCommandCompleteCallback = stubCompletionCallback;
    commandToSend.pCmdContext = NULL;
    commandToSend.pArgs = NULL;

    mqttAgentContext.agentInterface.pMsgCtx->pSentCommand = &commandToSend;

    /* Invoking mqttEventCallback with MQTT_PACKET_TYPE_PUBREL packet type.
     * MQTT_PACKET_TYPE_PUBREC packet type code path will also be covered
     * by this test case. */
    packetType = MQTT_PACKET_TYPE_PUBREL;

    MQTTAgentCommand_Publish_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTTAgentCommand_Publish_ReturnThruPtr_pReturnFlags( &returnFlags );
    MQTT_ProcessLoop_Stub( MQTT_ProcessLoop_CustomStub );

    mqttStatus = MQTTAgent_CommandLoop( &mqttAgentContext );

    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );
    /* Ensure that callback is invoked. */
    TEST_ASSERT_EQUAL( 1, commandCompleteCallbackCount );

    /* Invoking mqttEventCallback with MQTT_PACKET_TYPE_PINGRESP packet type. */
    commandCompleteCallbackCount = 0;
    packetType = MQTT_PACKET_TYPE_PINGRESP;

    MQTTAgentCommand_Publish_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTTAgentCommand_Publish_ReturnThruPtr_pReturnFlags( &returnFlags );
    MQTT_ProcessLoop_Stub( MQTT_ProcessLoop_CustomStub );

    mqttStatus = MQTTAgent_CommandLoop( &mqttAgentContext );

    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );
    /* Ensure that callback is invoked. */
    TEST_ASSERT_EQUAL( 1, commandCompleteCallbackCount );

    /* Invoking mqttEventCallback with MQTT_PACKET_TYPE_PUBACK packet type.
     * MQTT_PACKET_TYPE_PUBCOMP, MQTT_PACKET_TYPE_SUBACK, MQTT_PACKET_TYPE_UNSUBACK
     * packet types code path will also be covered by this test case. */
    packetType = MQTT_PACKET_TYPE_PUBACK;
    commandCompleteCallbackCount = 0;

    mqttAgentContext.pPendingAcks[ 0 ].packetId = 1U;
    command.pCommandCompleteCallback = stubCompletionCallback;
    mqttAgentContext.pPendingAcks[ 0 ].pOriginalCommand = &command;

    MQTTAgentCommand_Publish_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTTAgentCommand_Publish_ReturnThruPtr_pReturnFlags( &returnFlags );
    MQTT_ProcessLoop_Stub( MQTT_ProcessLoop_CustomStub );

    mqttStatus = MQTTAgent_CommandLoop( &mqttAgentContext );

    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );
    /* Ensure that callback is invoked. */
    TEST_ASSERT_EQUAL( 2, commandCompleteCallbackCount );
    /* Ensure that acknowledgment is cleared. */
    TEST_ASSERT_EQUAL( 0, mqttAgentContext.pPendingAcks[ 0 ].packetId );
    TEST_ASSERT_EQUAL( NULL, mqttAgentContext.pPendingAcks[ 0 ].pOriginalCommand );

    /* mqttEventcallback behavior when the command for the pending ack is NULL for the received PUBACK. */
    commandCompleteCallbackCount = 0;
    mqttAgentContext.pPendingAcks[ 0 ].packetId = 1U;
    mqttAgentContext.pPendingAcks[ 0 ].pOriginalCommand = NULL;
    MQTTAgentCommand_Publish_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTTAgentCommand_Publish_ReturnThruPtr_pReturnFlags( &returnFlags );
    MQTT_ProcessLoop_Stub( MQTT_ProcessLoop_CustomStub );

    mqttStatus = MQTTAgent_CommandLoop( &mqttAgentContext );

    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );
    /* Ensure that callback is invoked. */
    TEST_ASSERT_EQUAL( 1, commandCompleteCallbackCount );

    /* mqttEventcallback behavior when the packet Id 0 is received in the PUBACK. */
    packetIdentifier = 0U;
    commandCompleteCallbackCount = 0;
    mqttAgentContext.pPendingAcks[ 0 ].packetId = 0U;
    command.pCommandCompleteCallback = stubCompletionCallback;
    mqttAgentContext.pPendingAcks[ 0 ].pOriginalCommand = &command;

    MQTTAgentCommand_Publish_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTTAgentCommand_Publish_ReturnThruPtr_pReturnFlags( &returnFlags );
    MQTT_ProcessLoop_Stub( MQTT_ProcessLoop_CustomStub );

    mqttStatus = MQTTAgent_CommandLoop( &mqttAgentContext );

    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );
    /* Ensure that callback is invoked. */
    TEST_ASSERT_EQUAL( 1, commandCompleteCallbackCount );

    /* Test case checking no corresponding ack exists for the PUBACK received in the pPendingAcks array. */
    packetIdentifier = 1U;
    commandCompleteCallbackCount = 0;

    MQTTAgentCommand_Publish_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTTAgentCommand_Publish_ReturnThruPtr_pReturnFlags( &returnFlags );
    MQTT_ProcessLoop_Stub( MQTT_ProcessLoop_CustomStub );

    mqttStatus = MQTTAgent_CommandLoop( &mqttAgentContext );

    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );
    /* Ensure that callback is invoked. */
    TEST_ASSERT_EQUAL( 1, commandCompleteCallbackCount );

    /* Invoking mqttEventCallback with MQTT_PACKET_TYPE_SUBACK packet type. */
    packetType = MQTT_PACKET_TYPE_SUBACK;
    commandCompleteCallbackCount = 0;

    mqttAgentContext.pPendingAcks[ 0 ].packetId = 1U;
    command.pCommandCompleteCallback = NULL;
    mqttAgentContext.pPendingAcks[ 0 ].pOriginalCommand = &command;


    MQTTAgentCommand_Publish_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTTAgentCommand_Publish_ReturnThruPtr_pReturnFlags( &returnFlags );
    MQTT_ProcessLoop_Stub( MQTT_ProcessLoop_CustomStub );

    mqttStatus = MQTTAgent_CommandLoop( &mqttAgentContext );

    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );
    /* Ensure that callback is invoked. */
    TEST_ASSERT_EQUAL( 1, commandCompleteCallbackCount );
    /* Ensure that acknowledgment is cleared. */
    TEST_ASSERT_EQUAL( 0, mqttAgentContext.pPendingAcks[ 0 ].packetId );
    TEST_ASSERT_EQUAL( NULL, mqttAgentContext.pPendingAcks[ 0 ].pOriginalCommand );

    /* Invoking mqttEventCallback with MQTT_PACKET_TYPE_PUBLISH packet type. */
    packetType = MQTT_PACKET_TYPE_PUBLISH;
    commandCompleteCallbackCount = 0;

    MQTTAgentCommand_Publish_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTTAgentCommand_Publish_ReturnThruPtr_pReturnFlags( &returnFlags );
    MQTT_ProcessLoop_Stub( MQTT_ProcessLoop_CustomStub );

    mqttStatus = MQTTAgent_CommandLoop( &mqttAgentContext );

    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );
    /* Ensure that callback is invoked. */
    TEST_ASSERT_EQUAL( 1, commandCompleteCallbackCount );
    TEST_ASSERT_EQUAL( 1, publishCallbackCount );

    /* Test case when completion callback is NULL. */
    commandToSend.pCommandCompleteCallback = NULL;
    commandCompleteCallbackCount = 0;

    MQTTAgentCommand_Publish_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTTAgentCommand_Publish_ReturnThruPtr_pReturnFlags( &returnFlags );
    MQTT_ProcessLoop_Stub( MQTT_ProcessLoop_CustomStub );

    mqttStatus = MQTTAgent_CommandLoop( &mqttAgentContext );

    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );
    /* Ensure that callback is not invoked. */
    TEST_ASSERT_EQUAL( 0, commandCompleteCallbackCount );
}

/**
 * @brief Test mqttEventCallback invocation via MQTT_ProcessLoop.
 * TODO: Split this function up.
 */
void test_MQTTAgent_CommandLoop_InvalidCommand1( void )
{
    MQTTStatus_t mqttStatus;
    MQTTAgentContext_t mqttAgentContext;
    MQTTAgentCommand_t commandToSend = { 0 };

    /* Setting up MQTT Agent Context. */
    setupAgentContext( &mqttAgentContext );

    mqttAgentContext.mqttContext.connectStatus = MQTTConnected;
    returnFlags.addAcknowledgment = false;
    returnFlags.runProcessLoop = true;
    returnFlags.endLoop = true;

    MQTTAgentCommand_ProcessLoop_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTTAgentCommand_ProcessLoop_ReturnThruPtr_pReturnFlags( &returnFlags );

    /* Initializing command to be sent to the commandLoop. */
    commandToSend.commandType = NONE - 1;
    commandToSend.pCommandCompleteCallback = stubCompletionCallback;
    commandToSend.pCmdContext = NULL;
    commandToSend.pArgs = NULL;

    mqttAgentContext.agentInterface.pMsgCtx->pSentCommand = &commandToSend;

    /* Invoking mqttEventCallback with MQTT_PACKET_TYPE_PUBREL packet type.
     * MQTT_PACKET_TYPE_PUBREC packet type code path will also be covered
     * by this test case. */
    packetType = MQTT_PACKET_TYPE_PUBREL;

    MQTT_ProcessLoop_Stub( MQTT_ProcessLoop_CustomStub );

    mqttStatus = MQTTAgent_CommandLoop( &mqttAgentContext );

    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );
}

/**
 * @brief Test when only half data is received by the process loop.
 * TODO: Split this function up.
 */
void test_MQTTAgent_CommandLoop_NoCommand_NoData( void )
{
    MQTTStatus_t mqttStatus;
    MQTTAgentContext_t mqttAgentContext;
    MQTTAgentCommand_t commandToSend = { 0 };

    /* Setting up MQTT Agent Context. */
    setupAgentContext( &mqttAgentContext );

    mqttAgentContext.mqttContext.connectStatus = MQTTConnected;
    returnFlags.addAcknowledgment = false;
    returnFlags.runProcessLoop = true;
    returnFlags.endLoop = true;

    MQTTAgentCommand_ProcessLoop_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTTAgentCommand_ProcessLoop_ReturnThruPtr_pReturnFlags( &returnFlags );

    /* Initializing command to be sent to the commandLoop. */
    commandToSend.commandType = NONE - 1;
    commandToSend.pCommandCompleteCallback = stubCompletionCallback;
    commandToSend.pCmdContext = NULL;
    commandToSend.pArgs = NULL;

    mqttAgentContext.agentInterface.pMsgCtx->pSentCommand = &commandToSend;

    /* Invoking mqttEventCallback with MQTT_PACKET_TYPE_PUBREL packet type.
     * MQTT_PACKET_TYPE_PUBREC packet type code path will also be covered
     * by this test case. */
    packetType = MQTT_PACKET_TYPE_PUBREL;

    MQTT_ProcessLoop_Stub( MQTT_ProcessLoop_NeedMoreBytes );

    mqttStatus = MQTTAgent_CommandLoop( &mqttAgentContext );

    TEST_ASSERT_EQUAL( MQTTNeedMoreBytes, mqttStatus );
}

/**
 * @brief Test MQTTAgent_CommandLoop failure when second call to MQTT_ProcessLoop fails.
 */
void test_MQTTAgent_CommandLoop_second_processloop_fails( void )
{
    MQTTStatus_t mqttStatus;
    MQTTAgentContext_t mqttAgentContext;

    setupAgentContext( &mqttAgentContext );

    mqttAgentContext.mqttContext.connectStatus = MQTTConnected;
    returnFlags.addAcknowledgment = false;
    returnFlags.runProcessLoop = true;
    returnFlags.endLoop = false;

    MQTTAgentCommand_ProcessLoop_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTTAgentCommand_ProcessLoop_ReturnThruPtr_pReturnFlags( &returnFlags );

    /* The following stub ensures that the second or later call to
     * MQTT_ProcessLoop will fail. */
    MQTT_ProcessLoop_Stub( MQTT_ProcessLoop_FailSecondAndLaterCallsStub );

    /* MQTTAgent_CommandLoop keeps calling MQTT_ProcessLoop until an error occurs.
     * In this case, the second call to MQTT_ProcessLoop will error out (as ensured
     * by the above stub) and therefore, we expect the MQTTAgent_CommandLoop
     * to fail.*/
    mqttStatus = MQTTAgent_CommandLoop( &mqttAgentContext );

    TEST_ASSERT_EQUAL( MQTTRecvFailed, mqttStatus );
}

/**
 * @brief Test MQTTAgent_CommandLoop failure when executing second command in
 * the command queue fails.
 */
void test_MQTTAgent_CommandLoop_failure_executing_second_command( void )
{
    MQTTStatus_t mqttStatus;
    MQTTAgentContext_t mqttAgentContext;
    MQTTAgentCommand_t commandToSend = { 0 };

    setupAgentContext( &mqttAgentContext );

    mqttAgentContext.mqttContext.connectStatus = MQTTConnected;
    returnFlags.addAcknowledgment = false;
    returnFlags.runProcessLoop = true;
    returnFlags.endLoop = false;

    /* Initializing command to be sent to the commandLoop. */
    commandToSend.commandType = PUBLISH;
    commandToSend.pCommandCompleteCallback = stubCompletionCallback;
    commandToSend.pCmdContext = NULL;
    commandToSend.pArgs = NULL;

    mqttAgentContext.agentInterface.pMsgCtx->pSentCommand = &commandToSend;

    MQTTAgentCommand_Publish_ExpectAnyArgsAndReturn( MQTTSuccess );
    MQTTAgentCommand_Publish_ReturnThruPtr_pReturnFlags( &returnFlags );
    MQTT_ProcessLoop_ExpectAnyArgsAndReturn( MQTTSuccess );

    /* The stubReceive function ensures that the CommandLoop keeps getting the
     * same command again and again. Ensure that the second PUBLISH fails. */
    MQTTAgentCommand_Publish_ExpectAnyArgsAndReturn( MQTTSendFailed );

    mqttStatus = MQTTAgent_CommandLoop( &mqttAgentContext );

    TEST_ASSERT_EQUAL( MQTTSendFailed, mqttStatus );
    /* Ensure that callback is invoked. */
    TEST_ASSERT_EQUAL( 2, commandCompleteCallbackCount );
}

void test_MQTTAgent_CancelAll( void )
{
    MQTTAgentContext_t mqttAgentContext = { 0 };
    MQTTStatus_t mqttStatus;
    MQTTAgentCommand_t command = { 0 };
    MQTTAgentCommandContext_t commandContext = { 0 };

    setupAgentContext( &mqttAgentContext );

    command.pCommandCompleteCallback = stubCompletionCallback;
    command.pCmdContext = &commandContext;
    globalMessageContext.pSentCommand = &command;

    mqttAgentContext.pPendingAcks[ 0 ].packetId = 1U;
    mqttAgentContext.pPendingAcks[ 0 ].pOriginalCommand = &command;

    /* Invalid parameters. */
    mqttStatus = MQTTAgent_CancelAll( NULL );
    TEST_ASSERT_EQUAL( MQTTBadParameter, mqttStatus );

    mqttAgentContext.agentInterface.pMsgCtx = NULL;
    mqttStatus = MQTTAgent_CancelAll( &mqttAgentContext );
    TEST_ASSERT_EQUAL( MQTTBadParameter, mqttStatus );

    /* Only receive a few commands to avoid infinite loop. */
    mqttAgentContext.agentInterface.recv = stubReceiveThenFail;
    mqttAgentContext.agentInterface.pMsgCtx = &globalMessageContext;
    mqttStatus = MQTTAgent_CancelAll( &mqttAgentContext );
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );

    /* Ensure that callback is invoked. */
    TEST_ASSERT_EQUAL( 2, commandCompleteCallbackCount );
    TEST_ASSERT_EQUAL( MQTTRecvFailed, command.pCmdContext->returnStatus );


    /* Ensure that acknowledgment is cleared. */
    TEST_ASSERT_EQUAL( 0, mqttAgentContext.pPendingAcks[ 0 ].packetId );
    TEST_ASSERT_EQUAL( NULL, mqttAgentContext.pPendingAcks[ 0 ].pOriginalCommand );

    /* Ensure that command is released. */
    TEST_ASSERT_EQUAL( 2, commandReleaseCallCount );

    /* Test MQTTAgent_CancelAll() with commandCallback as null. */
    receiveCounter = 0;
    commandCompleteCallbackCount = 0;
    commandReleaseCallCount = 0;
    command.pCommandCompleteCallback = NULL;
    mqttAgentContext.agentInterface.pMsgCtx->pSentCommand = &command;
    mqttAgentContext.pPendingAcks[ 0 ].packetId = 1U;
    mqttAgentContext.pPendingAcks[ 0 ].pOriginalCommand = &command;

    mqttStatus = MQTTAgent_CancelAll( &mqttAgentContext );

    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );

    /* Ensure that callback is not invoked. */
    TEST_ASSERT_EQUAL( 0, commandCompleteCallbackCount );

    /* Ensure that acknowledgment is cleared. */
    TEST_ASSERT_EQUAL( 0, mqttAgentContext.pPendingAcks[ 0 ].packetId );
    TEST_ASSERT_EQUAL( NULL, mqttAgentContext.pPendingAcks[ 0 ].pOriginalCommand );

    /* Ensure that command is released. */
    TEST_ASSERT_EQUAL( 2, commandReleaseCallCount );
}
