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
 * @file core_mqtt_agent.c
 * @brief Implements an MQTT agent (or daemon task) to enable multithreaded access to
 * coreMQTT.
 *
 * @note Implements an MQTT agent (or daemon task) on top of the coreMQTT MQTT client
 * library.  The agent makes coreMQTT usage thread safe by being the only task (or
 * thread) in the system that is allowed to access the native coreMQTT API - and in
 * so doing, serializes all access to coreMQTT even when multiple tasks are using the
 * same MQTT connection.
 *
 * The agent provides an equivalent API for each coreMQTT API.  Whereas coreMQTT
 * APIs are prefixed "MQTT_", the agent APIs are prefixed "MQTTAgent_".  For example,
 * that agent's MQTTAgent_Publish() API is the thread safe equivalent to coreMQTT's
 * MQTT_Publish() API.
 */

/* Standard includes. */
#include <string.h>
#include <stdio.h>
#include <assert.h>

/* MQTT agent include. */
#include "core_mqtt_agent.h"
#include "core_mqtt_agent_command_functions.h"

/* MQTT Agent default logging configuration include. */
#include "core_mqtt_agent_default_logging.h"

/*-----------------------------------------------------------*/

#if ( MQTT_AGENT_USE_QOS_1_2_PUBLISH != 0 )

/**
 * @brief Array used to maintain the outgoing publish records and their
 * state by the coreMQTT library.
 */
    static MQTTPubAckInfo_t pOutgoingPublishRecords[ MQTT_AGENT_MAX_OUTSTANDING_ACKS ];

/**
 * @brief Array used to maintain the incoming publish records and their
 * state by the coreMQTT library.
 */
    static MQTTPubAckInfo_t pIncomingPublishRecords[ MQTT_AGENT_MAX_OUTSTANDING_ACKS ];
#endif

/**
 * @brief Track an operation by adding it to a list, indicating it is anticipating
 * an acknowledgment.
 *
 * @param[in] pAgentContext Agent context for the MQTT connection.
 * @param[in] packetId Packet ID of pending ack.
 * @param[in] pCommand Pointer to command that is expecting an ack.
 *
 * @return Returns one of the following:
 * - #MQTTSuccess if an entry was added for the to the list.
 * - #MQTTStateCollision if there already exists an entry for the same packet ID
 * in the list.
 * - #MQTTNoMemory if there is no space available in the list for adding a
 * new entry.
 */
static MQTTStatus_t addAwaitingOperation( MQTTAgentContext_t * pAgentContext,
                                          uint16_t packetId,
                                          MQTTAgentCommand_t * pCommand );

/**
 * @brief Retrieve an operation from the list of pending acks, and optionally
 * remove it from the list.
 *
 * @param[in] pAgentContext Agent context for the MQTT connection.
 * @param[in] incomingPacketId Packet ID of incoming ack.
 *
 * @return Pointer to stored information about the operation awaiting the ack.
 * Returns NULL if the packet ID is zero or original command does not exist.
 */
static MQTTAgentAckInfo_t * getAwaitingOperation( MQTTAgentContext_t * pAgentContext,
                                                  uint16_t incomingPacketId );

/**
 * @brief Populate the parameters of a #MQTTAgentCommand struct.
 *
 * @param[in] commandType Type of command.  For example, publish or subscribe.
 * @param[in] pMqttAgentContext Pointer to MQTT context to use for command.
 * @param[in] pMqttInfoParam Pointer to MQTTPublishInfo_t or MQTTSubscribeInfo_t.
 * @param[in] commandCompleteCallback Callback for when command completes.
 * @param[in] pCommandCompleteCallbackContext Context and necessary structs for command.
 * @param[out] pCommand Pointer to initialized command.
 *
 * @return #MQTTSuccess if all necessary fields for the command are passed,
 * else an enumerated error code.
 */
static MQTTStatus_t createCommand( MQTTAgentCommandType_t commandType,
                                   const MQTTAgentContext_t * pMqttAgentContext,
                                   void * pMqttInfoParam,
                                   MQTTAgentCommandCallback_t commandCompleteCallback,
                                   MQTTAgentCommandContext_t * pCommandCompleteCallbackContext,
                                   MQTTAgentCommand_t * pCommand );

/**
 * @brief Add a command to the global command queue.
 *
 * @param[in] pAgentContext Agent context for the MQTT connection.
 * @param[in] pCommand Pointer to command to copy to queue.
 * @param[in] blockTimeMs The maximum amount of time to milliseconds to wait in the
 * Blocked state (so not consuming any CPU time) for the command to be posted to the
 * queue should the queue already be full.
 *
 * @return #MQTTSuccess if the command was added to the queue, else an enumerated
 * error code.
 */
static MQTTStatus_t addCommandToQueue( const MQTTAgentContext_t * pAgentContext,
                                       MQTTAgentCommand_t * pCommand,
                                       uint32_t blockTimeMs );

/**
 * @brief Process a #MQTTAgentCommand struct.
 *
 * @note This agent does not check existing subscriptions before sending a
 * SUBSCRIBE or UNSUBSCRIBE packet. If a subscription already exists, then
 * a SUBSCRIBE packet will be sent anyway, and if multiple tasks are subscribed
 * to a topic filter, then they will all be unsubscribed after an UNSUBSCRIBE.
 *
 * @param[in] pMqttAgentContext Agent context for MQTT connection.
 * @param[in] pCommand Pointer to command to process.
 * @param[out] pEndLoop Whether the command loop should terminate.
 *
 * @return status of MQTT library API call.
 */
static MQTTStatus_t processCommand( MQTTAgentContext_t * pMqttAgentContext,
                                    MQTTAgentCommand_t * pCommand,
                                    bool * pEndLoop );

/**
 * @brief Dispatch incoming publishes and acks to their various handler functions.
 *
 * @param[in] pMqttContext MQTT Context
 * @param[in] pPacketInfo Pointer to incoming packet.
 * @param[in] pDeserializedInfo Pointer to deserialized information from
 * the incoming packet.
 */
static void mqttEventCallback( MQTTContext_t * pMqttContext,
                               MQTTPacketInfo_t * pPacketInfo,
                               MQTTDeserializedInfo_t * pDeserializedInfo );

/**
 * @brief Mark a command as complete after receiving an acknowledgment packet.
 *
 * @param[in] pAgentContext Agent context for the MQTT connection.
 * @param[in] pPacketInfo Pointer to incoming packet.
 * @param[in] pDeserializedInfo Pointer to deserialized information from
 * the incoming packet.
 * @param[in] pAckInfo Pointer to stored information for the original operation
 * resulting in the received packet.
 * @param[in] packetType The type of the incoming packet, either SUBACK, UNSUBACK,
 * PUBACK, or PUBCOMP.
 */
static void handleAcks( const MQTTAgentContext_t * pAgentContext,
                        const MQTTPacketInfo_t * pPacketInfo,
                        const MQTTDeserializedInfo_t * pDeserializedInfo,
                        MQTTAgentAckInfo_t * pAckInfo,
                        uint8_t packetType );

/**
 * @brief Retrieve a pointer to an agent context given an MQTT context.
 *
 * @param[in] pMQTTContext MQTT Context to search for.
 *
 * @return Pointer to agent context, or NULL.
 */
static MQTTAgentContext_t * getAgentFromMQTTContext( MQTTContext_t * pMQTTContext );

/**
 * @brief Helper function for creating a command and adding it to the command
 * queue.
 *
 * @param[in] commandType Type of command.
 * @param[in] pMqttAgentContext Handle of the MQTT connection to use.
 * @param[in] pCommandCompleteCallbackContext Context and necessary structs for command.
 * @param[in] commandCompleteCallback Callback for when command completes.
 * @param[in] pMqttInfoParam Pointer to command argument.
 * @param[in] blockTimeMs Maximum amount of time in milliseconds to wait (in the
 * Blocked state, so not consuming any CPU time) for the command to be posted to the
 * MQTT agent should the MQTT agent's event queue be full.
 *
 * @return #MQTTSuccess if the command was posted to the MQTT agent's event queue.
 * Otherwise an enumerated error code.
 */
static MQTTStatus_t createAndAddCommand( MQTTAgentCommandType_t commandType,
                                         const MQTTAgentContext_t * pMqttAgentContext,
                                         void * pMqttInfoParam,
                                         MQTTAgentCommandCallback_t commandCompleteCallback,
                                         MQTTAgentCommandContext_t * pCommandCompleteCallbackContext,
                                         uint32_t blockTimeMs );

/**
 * @brief Helper function to mark a command as complete and invoke its callback.
 * This function calls the releaseCommand callback.
 *
 * @param[in] pAgentContext Agent context for the MQTT connection.
 * @param[in] pCommand Command to complete.
 * @param[in] returnCode Return status of command.
 * @param[in] pSubackCodes Pointer to suback array, if command is a SUBSCRIBE.
 */
static void concludeCommand( const MQTTAgentContext_t * pAgentContext,
                             MQTTAgentCommand_t * pCommand,
                             MQTTStatus_t returnCode,
                             uint8_t * pSubackCodes );

/**
 * @brief Resend QoS 1 and 2 publishes after resuming a session.
 *
 * @param[in] pMqttAgentContext Agent context for the MQTT connection.
 *
 * @return #MQTTSuccess if all publishes resent successfully, else error code
 * from #MQTT_Publish.
 */
static MQTTStatus_t resendPublishes( MQTTAgentContext_t * pMqttAgentContext );

/**
 * @brief Clears the list of pending acknowledgments by invoking each callback
 * with #MQTTRecvFailed either for ALL operations in the list OR only for
 * Subscribe/Unsubscribe operations.
 *
 * @param[in] pMqttAgentContext Agent context of the MQTT connection.
 * @param[in] clearOnlySubUnsubEntries Flag indicating whether all entries OR
 * entries pertaining to only Subscribe/Unsubscribe operations should be cleaned
 * from the list.
 */
static void clearPendingAcknowledgments( MQTTAgentContext_t * pMqttAgentContext,
                                         bool clearOnlySubUnsubEntries );

/**
 * @brief Validate an #MQTTAgentContext_t and a #MQTTAgentCommandInfo_t from API
 * functions.
 *
 * @param[in] pMqttAgentContext #MQTTAgentContext_t to validate.
 * @param[in] pCommandInfo #MQTTAgentCommandInfo_t to validate.
 *
 * @return `true` if parameters are valid, else `false`.
 */
static bool validateStruct( const MQTTAgentContext_t * pMqttAgentContext,
                            const MQTTAgentCommandInfo_t * pCommandInfo );

/**
 * @brief Validate the parameters for a CONNECT, SUBSCRIBE, UNSUBSCRIBE
 * or PUBLISH.
 *
 * @param[in] commandType CONNECT, SUBSCRIBE, UNSUBSCRIBE, or PUBLISH.
 * @param[in] pParams Parameter structure to validate.
 *
 * @return `true` if parameter structure is valid, else `false`.
 */
static bool validateParams( MQTTAgentCommandType_t commandType,
                            const void * pParams );

/**
 * @brief Called before accepting any PUBLISH or SUBSCRIBE messages to check
 * there is space in the pending ACK list for the outgoing PUBLISH or SUBSCRIBE.
 *
 * @note Because the MQTT agent is inherently multi threaded, and this function
 * is called from the context of the application task and not the MQTT agent
 * task, this function can only return a best effort result.  It can definitely
 * say if there is space for a new pending ACK when the function is called, but
 * the case of space being exhausted when the agent executes a command that
 * results in an ACK must still be handled.
 *
 * @param[in] pAgentContext Pointer to the context for the MQTT connection to
 * which the PUBLISH or SUBSCRIBE message is to be sent.
 *
 * @return true if there is space in that MQTT connection's ACK list, otherwise
 * false;
 */
static bool isSpaceInPendingAckList( const MQTTAgentContext_t * pAgentContext );

/*-----------------------------------------------------------*/

static bool isSpaceInPendingAckList( const MQTTAgentContext_t * pAgentContext )
{
    const MQTTAgentAckInfo_t * pendingAcks;
    bool spaceFound = false;
    size_t i;

    assert( pAgentContext != NULL );

    pendingAcks = pAgentContext->pPendingAcks;

    /* Are there any open slots? */
    for( i = 0; i < MQTT_AGENT_MAX_OUTSTANDING_ACKS; i++ )
    {
        /* If the packetId is MQTT_PACKET_ID_INVALID then the array space is
         * not in use. */
        if( pendingAcks[ i ].packetId == MQTT_PACKET_ID_INVALID )
        {
            spaceFound = true;
            break;
        }
    }

    return spaceFound;
}

/*-----------------------------------------------------------*/

static MQTTStatus_t addAwaitingOperation( MQTTAgentContext_t * pAgentContext,
                                          uint16_t packetId,
                                          MQTTAgentCommand_t * pCommand )
{
    size_t i = 0, unusedPos = MQTT_AGENT_MAX_OUTSTANDING_ACKS;
    MQTTStatus_t status = MQTTNoMemory;
    MQTTAgentAckInfo_t * pendingAcks = NULL;

    assert( pAgentContext != NULL );
    assert( pCommand != NULL );
    assert( packetId != MQTT_PACKET_ID_INVALID );
    pendingAcks = pAgentContext->pPendingAcks;

    /* Before adding the record for the pending acknowledgement of the packet ID,
     * make sure that there doesn't already exist an entry for the same packet ID.
     * Also, as part of iterating through the list of pending acknowledgements,
     * find an unused space for the packet ID to be added, if it can be. */
    for( i = 0; i < MQTT_AGENT_MAX_OUTSTANDING_ACKS; i++ )
    {
        /* If the packetId is MQTT_PACKET_ID_INVALID then the array space is not in
         * use. */
        if( ( unusedPos == MQTT_AGENT_MAX_OUTSTANDING_ACKS ) &&
            ( pendingAcks[ i ].packetId == MQTT_PACKET_ID_INVALID ) )
        {
            unusedPos = i;
            status = MQTTSuccess;
        }

        if( pendingAcks[ i ].packetId == packetId )
        {
            /* Check whether there exists a duplicate entry for pending
             * acknowledgment for the same packet ID that we want to add to
             * the list.
             * Note: This is an unlikely edge case which represents that a packet ID
             * didn't receive acknowledgment, but subsequent SUBSCRIBE/PUBLISH operations
             * representing 65535 packet IDs were successful that caused the bit packet
             * ID value to wrap around and reached the same packet ID as that was still
             * pending acknowledgment.
             */
            status = MQTTStateCollision;
            LogError( ( "Failed to add operation to list of pending acknowledgments: "
                        "Existing entry found for same packet: PacketId=%u\n", packetId ) );
            break;
        }
    }

    /* Add the packet ID to the list if there is space available, and there is no
     * duplicate entry for the same packet ID found. */
    if( status == MQTTSuccess )
    {
        pendingAcks[ unusedPos ].packetId = packetId;
        pendingAcks[ unusedPos ].pOriginalCommand = pCommand;
    }
    else if( status == MQTTNoMemory )
    {
        LogError( ( "Failed to add operation to list of pending acknowledgments: "
                    "No memory available: PacketId=%u\n", packetId ) );
    }
    else
    {
        /* Empty else MISRA 15.7 */
    }

    return status;
}

/*-----------------------------------------------------------*/

static MQTTAgentAckInfo_t * getAwaitingOperation( MQTTAgentContext_t * pAgentContext,
                                                  uint16_t incomingPacketId )
{
    size_t i = 0;
    MQTTAgentAckInfo_t * pFoundAck = NULL;

    assert( pAgentContext != NULL );

    /* Look through the array of packet IDs that are still waiting to be acked to
     * find one with incomingPacketId. */
    for( i = 0; i < MQTT_AGENT_MAX_OUTSTANDING_ACKS; i++ )
    {
        if( pAgentContext->pPendingAcks[ i ].packetId == incomingPacketId )
        {
            pFoundAck = &( pAgentContext->pPendingAcks[ i ] );
            break;
        }
    }

    if( pFoundAck == NULL )
    {
        LogError( ( "No ack found for packet id %u.\n", incomingPacketId ) );
    }
    else if( ( pFoundAck->pOriginalCommand == NULL ) || ( pFoundAck->packetId == 0U ) )
    {
        LogError( ( "Found ack had empty fields. PacketId=%hu, Original Command=%p",
                    ( unsigned short ) pFoundAck->packetId,
                    ( void * ) pFoundAck->pOriginalCommand ) );
        ( void ) memset( pFoundAck, 0x00, sizeof( MQTTAgentAckInfo_t ) );
        pFoundAck = NULL;
    }
    else
    {
        /* Empty else MISRA 15.7 */
    }

    return pFoundAck;
}

/*-----------------------------------------------------------*/

static MQTTStatus_t createCommand( MQTTAgentCommandType_t commandType,
                                   const MQTTAgentContext_t * pMqttAgentContext,
                                   void * pMqttInfoParam,
                                   MQTTAgentCommandCallback_t commandCompleteCallback,
                                   MQTTAgentCommandContext_t * pCommandCompleteCallbackContext,
                                   MQTTAgentCommand_t * pCommand )
{
    bool isValid, isSpace = true;
    MQTTStatus_t statusReturn;
    const MQTTPublishInfo_t * pPublishInfo;
    size_t uxHeaderBytes;
    const size_t uxControlAndLengthBytes = ( size_t ) 4; /* Control, remaining length and length bytes. */

    assert( pMqttAgentContext != NULL );
    assert( pCommand != NULL );

    ( void ) memset( pCommand, 0x00, sizeof( MQTTAgentCommand_t ) );

    /* Determine if required parameters are present in context. */
    switch( commandType )
    {
        case SUBSCRIBE:
        case UNSUBSCRIBE:
            assert( pMqttInfoParam != NULL );

            /* This message type results in the broker returning an ACK.  The
             * agent maintains an array of outstanding ACK messages.  See if
             * the array contains space for another outstanding ack. */
            isSpace = isSpaceInPendingAckList( pMqttAgentContext );

            isValid = isSpace;

            break;

        case PUBLISH:
            pPublishInfo = ( const MQTTPublishInfo_t * ) pMqttInfoParam;

            /* Calculate the space consumed by everything other than the
             * payload. */
            uxHeaderBytes = uxControlAndLengthBytes;
            uxHeaderBytes += pPublishInfo->topicNameLength;

            /* This message type results in the broker returning an ACK. The
             * agent maintains an array of outstanding ACK messages.  See if
             * the array contains space for another outstanding ack.  QoS0
             * publish does not result in an ack so it doesn't matter if
             * there is no space in the ACK array. */
            if( pPublishInfo->qos != MQTTQoS0 )
            {
                isSpace = isSpaceInPendingAckList( pMqttAgentContext );
            }

            /* Will the message fit in the defined buffer? */
            isValid = ( uxHeaderBytes < pMqttAgentContext->mqttContext.networkBuffer.size ) &&
                      ( isSpace == true );

            break;

        case PROCESSLOOP:
        case PING:
        case CONNECT:
        case DISCONNECT:
        default:
            /* Other operations don't need to store ACKs. */
            isValid = true;
            break;
    }

    if( isValid )
    {
        pCommand->commandType = commandType;
        pCommand->pArgs = pMqttInfoParam;
        pCommand->pCmdContext = pCommandCompleteCallbackContext;
        pCommand->pCommandCompleteCallback = commandCompleteCallback;
    }

    statusReturn = ( isValid ) ? MQTTSuccess : MQTTBadParameter;

    if( ( statusReturn == MQTTBadParameter ) && ( isSpace == false ) )
    {
        /* The error was caused not by a bad parameter, but because there was
         * no room in the pending Ack list for the Ack response to an outgoing
         * PUBLISH or SUBSCRIBE message. */
        statusReturn = MQTTNoMemory;
    }

    return statusReturn;
}

/*-----------------------------------------------------------*/

static MQTTStatus_t addCommandToQueue( const MQTTAgentContext_t * pAgentContext,
                                       MQTTAgentCommand_t * pCommand,
                                       uint32_t blockTimeMs )
{
    bool queueStatus;

    assert( pAgentContext != NULL );
    assert( pCommand != NULL );

    /* The application called an API function.  The API function was validated and
     * packed into a MQTTAgentCommand_t structure.  Now post a reference to the MQTTAgentCommand_t
     * structure to the MQTT agent for processing. */
    queueStatus = pAgentContext->agentInterface.send(
        pAgentContext->agentInterface.pMsgCtx,
        &pCommand,
        blockTimeMs
        );

    return ( queueStatus ) ? MQTTSuccess : MQTTSendFailed;
}

/*-----------------------------------------------------------*/

static MQTTStatus_t processCommand( MQTTAgentContext_t * pMqttAgentContext,
                                    MQTTAgentCommand_t * pCommand,
                                    bool * pEndLoop )
{
    const MQTTAgentCommandFunc_t pCommandFunctionTable[ NUM_COMMANDS ] = MQTT_AGENT_FUNCTION_TABLE;
    MQTTStatus_t operationStatus = MQTTSuccess;
    bool ackAdded = false;
    MQTTAgentCommandFunc_t commandFunction = NULL;
    void * pCommandArgs = NULL;
    MQTTAgentCommandFuncReturns_t commandOutParams = { 0 };

    assert( pMqttAgentContext != NULL );
    assert( pEndLoop != NULL );

    if( pCommand != NULL )
    {
        assert( pCommand->commandType < NUM_COMMANDS );

        if( ( pCommand->commandType >= NONE ) && ( pCommand->commandType < NUM_COMMANDS ) )
        {
            commandFunction = pCommandFunctionTable[ pCommand->commandType ];
            pCommandArgs = pCommand->pArgs;
        }
        else
        {
            LogWarn( ( "An incorrect command type was received by the processCommand function."
                       " Type = %d.", pCommand->commandType ) );
            commandFunction = pCommandFunctionTable[ NONE ];
        }
    }
    else
    {
        commandFunction = pCommandFunctionTable[ NONE ];
    }

    operationStatus = commandFunction( pMqttAgentContext, pCommandArgs, &commandOutParams );

    if( ( operationStatus == MQTTSuccess ) &&
        commandOutParams.addAcknowledgment &&
        ( commandOutParams.packetId != MQTT_PACKET_ID_INVALID ) )
    {
        operationStatus = addAwaitingOperation( pMqttAgentContext, commandOutParams.packetId, pCommand );
        ackAdded = ( operationStatus == MQTTSuccess );
    }

    if( ( pCommand != NULL ) && ( ackAdded != true ) )
    {
        /* The command is complete, call the callback. */
        concludeCommand( pMqttAgentContext, pCommand, operationStatus, NULL );
    }

    /* Run the process loop if there were no errors and the MQTT connection
     * still exists. */
    if( ( operationStatus == MQTTSuccess ) && commandOutParams.runProcessLoop )
    {
        do
        {
            pMqttAgentContext->packetReceivedInLoop = false;

            if( ( ( operationStatus == MQTTSuccess ) || ( operationStatus == MQTTNeedMoreBytes ) ) &&
                ( pMqttAgentContext->mqttContext.connectStatus == MQTTConnected ) )
            {
                operationStatus = MQTT_ProcessLoop( &( pMqttAgentContext->mqttContext ) );
            }
        } while( pMqttAgentContext->packetReceivedInLoop );
    }

    /* Set the flag to break from the command loop. */
    *pEndLoop = ( commandOutParams.endLoop || ( operationStatus != MQTTSuccess ) );

    return operationStatus;
}

/*-----------------------------------------------------------*/

static void handleAcks( const MQTTAgentContext_t * pAgentContext,
                        const MQTTPacketInfo_t * pPacketInfo,
                        const MQTTDeserializedInfo_t * pDeserializedInfo,
                        MQTTAgentAckInfo_t * pAckInfo,
                        uint8_t packetType )
{
    uint8_t * pSubackCodes = NULL;

    assert( pAckInfo != NULL );
    assert( pAckInfo->pOriginalCommand != NULL );

    /* A SUBACK's status codes start 2 bytes after the variable header. */
    pSubackCodes = ( packetType == MQTT_PACKET_TYPE_SUBACK ) ? ( pPacketInfo->pRemainingData + 2U ) : NULL;

    concludeCommand( pAgentContext,
                     pAckInfo->pOriginalCommand,
                     pDeserializedInfo->deserializationResult,
                     pSubackCodes );

    /* Clear the entry from the list. */
    ( void ) memset( pAckInfo, 0x00, sizeof( MQTTAgentAckInfo_t ) );
}

/*-----------------------------------------------------------*/

static MQTTAgentContext_t * getAgentFromMQTTContext( MQTTContext_t * pMQTTContext )
{
    MQTTAgentContext_t ctx = { 0 };
    ptrdiff_t offset = ( ( uint8_t * ) &( ctx.mqttContext ) ) - ( ( uint8_t * ) &ctx );

    return ( MQTTAgentContext_t * ) &( ( ( uint8_t * ) pMQTTContext )[ 0 - offset ] );
}

/*-----------------------------------------------------------*/

static void mqttEventCallback( MQTTContext_t * pMqttContext,
                               MQTTPacketInfo_t * pPacketInfo,
                               MQTTDeserializedInfo_t * pDeserializedInfo )
{
    MQTTAgentAckInfo_t * pAckInfo;
    uint16_t packetIdentifier = pDeserializedInfo->packetIdentifier;
    MQTTAgentContext_t * pAgentContext;
    const uint8_t upperNibble = ( uint8_t ) 0xF0;

    assert( pMqttContext != NULL );
    assert( pPacketInfo != NULL );

    pAgentContext = getAgentFromMQTTContext( pMqttContext );

    /* This callback executes from within MQTT_ProcessLoop().  Setting this flag
     * indicates that the callback executed so the caller of MQTT_ProcessLoop() knows
     * it should call it again as there may be more data to process. */
    pAgentContext->packetReceivedInLoop = true;

    /* Handle incoming publish. The lower 4 bits of the publish packet type is used
     * for the dup, QoS, and retain flags. Hence masking out the lower bits to check
     * if the packet is publish. */
    if( ( pPacketInfo->type & upperNibble ) == MQTT_PACKET_TYPE_PUBLISH )
    {
        pAgentContext->pIncomingCallback( pAgentContext, packetIdentifier, pDeserializedInfo->pPublishInfo );
    }
    else
    {
        /* Handle other packets. */
        switch( pPacketInfo->type )
        {
            case MQTT_PACKET_TYPE_PUBACK:
            case MQTT_PACKET_TYPE_PUBCOMP:
            case MQTT_PACKET_TYPE_SUBACK:
            case MQTT_PACKET_TYPE_UNSUBACK:
                pAckInfo = getAwaitingOperation( pAgentContext, packetIdentifier );

                if( pAckInfo != NULL )
                {
                    /* This function will also clear the memory associated with
                     * the ack list entry. */
                    handleAcks( pAgentContext,
                                pPacketInfo,
                                pDeserializedInfo,
                                pAckInfo,
                                pPacketInfo->type );
                }
                else
                {
                    LogError( ( "No operation found matching packet id %u.\n", packetIdentifier ) );
                }

                break;

            /* Nothing to do for these packets since they don't indicate command completion. */
            case MQTT_PACKET_TYPE_PUBREC:
            case MQTT_PACKET_TYPE_PUBREL:
                break;

            /* Any other packet type is invalid. */
            case MQTT_PACKET_TYPE_PINGRESP:
            default:
                LogError( ( "Unknown packet type received:(%02x).\n",
                            pPacketInfo->type ) );
                break;
        }
    }
}

/*-----------------------------------------------------------*/

static MQTTStatus_t createAndAddCommand( MQTTAgentCommandType_t commandType,
                                         const MQTTAgentContext_t * pMqttAgentContext,
                                         void * pMqttInfoParam,
                                         MQTTAgentCommandCallback_t commandCompleteCallback,
                                         MQTTAgentCommandContext_t * pCommandCompleteCallbackContext,
                                         uint32_t blockTimeMs )
{
    MQTTStatus_t statusReturn = MQTTBadParameter;
    MQTTAgentCommand_t * pCommand;
    bool commandReleased = false;

    /* If the packet ID is zero then the MQTT context has not been initialized as 0
     * is the initial value but not a valid packet ID. */
    if( pMqttAgentContext->mqttContext.nextPacketId != MQTT_PACKET_ID_INVALID )
    {
        pCommand = pMqttAgentContext->agentInterface.getCommand( blockTimeMs );

        if( pCommand != NULL )
        {
            statusReturn = createCommand( commandType,
                                          pMqttAgentContext,
                                          pMqttInfoParam,
                                          commandCompleteCallback,
                                          pCommandCompleteCallbackContext,
                                          pCommand );

            if( statusReturn == MQTTSuccess )
            {
                statusReturn = addCommandToQueue( pMqttAgentContext, pCommand, blockTimeMs );
            }

            if( statusReturn != MQTTSuccess )
            {
                /* Could not send the command to the queue so release the command
                 * structure again. */
                commandReleased = pMqttAgentContext->agentInterface.releaseCommand( pCommand );

                if( !commandReleased )
                {
                    LogError( ( "Command %p could not be released.",
                                ( void * ) pCommand ) );
                }
            }
        }
        else
        {
            /* Ran out of MQTTAgentCommand_t structures - pool is empty. */
            statusReturn = MQTTNoMemory;
        }
    }
    else
    {
        LogError( ( "MQTT context must be initialized." ) );
    }

    return statusReturn;
}

/*-----------------------------------------------------------*/

static void concludeCommand( const MQTTAgentContext_t * pAgentContext,
                             MQTTAgentCommand_t * pCommand,
                             MQTTStatus_t returnCode,
                             uint8_t * pSubackCodes )
{
    bool commandReleased = false;
    MQTTAgentReturnInfo_t returnInfo;

    ( void ) memset( &returnInfo, 0x00, sizeof( MQTTAgentReturnInfo_t ) );
    assert( pAgentContext != NULL );
    assert( pAgentContext->agentInterface.releaseCommand != NULL );
    assert( pCommand != NULL );

    returnInfo.returnCode = returnCode;
    returnInfo.pSubackCodes = pSubackCodes;

    if( pCommand->pCommandCompleteCallback != NULL )
    {
        pCommand->pCommandCompleteCallback( pCommand->pCmdContext, &returnInfo );
    }

    commandReleased = pAgentContext->agentInterface.releaseCommand( pCommand );

    if( !commandReleased )
    {
        LogError( ( "Failed to release command %p of type %d.",
                    ( void * ) pCommand,
                    pCommand->commandType ) );
    }
}

/*-----------------------------------------------------------*/

static MQTTStatus_t resendPublishes( MQTTAgentContext_t * pMqttAgentContext )
{
    MQTTStatus_t statusResult = MQTTSuccess;
    MQTTStateCursor_t cursor = MQTT_STATE_CURSOR_INITIALIZER;
    uint16_t packetId = MQTT_PACKET_ID_INVALID;
    MQTTAgentAckInfo_t * pFoundAck = NULL;
    MQTTPublishInfo_t * pOriginalPublish = NULL;
    MQTTContext_t * pMqttContext;

    assert( pMqttAgentContext != NULL );
    pMqttContext = &( pMqttAgentContext->mqttContext );

    packetId = MQTT_PublishToResend( pMqttContext, &cursor );

    while( packetId != MQTT_PACKET_ID_INVALID )
    {
        /* Retrieve the operation but do not remove it from the list. */
        pFoundAck = getAwaitingOperation( pMqttAgentContext, packetId );

        if( pFoundAck != NULL )
        {
            /* Set the DUP flag. */
            pOriginalPublish = ( MQTTPublishInfo_t * ) ( pFoundAck->pOriginalCommand->pArgs );
            pOriginalPublish->dup = true;
            statusResult = MQTT_Publish( pMqttContext, pOriginalPublish, packetId );

            if( statusResult != MQTTSuccess )
            {
                concludeCommand( pMqttAgentContext, pFoundAck->pOriginalCommand, statusResult, NULL );
                ( void ) memset( pFoundAck, 0x00, sizeof( MQTTAgentAckInfo_t ) );
                LogError( ( "Failed to resend publishes. Error code=%s\n", MQTT_Status_strerror( statusResult ) ) );
                break;
            }
        }

        packetId = MQTT_PublishToResend( pMqttContext, &cursor );
    }

    return statusResult;
}

/*-----------------------------------------------------------*/

static void clearPendingAcknowledgments( MQTTAgentContext_t * pMqttAgentContext,
                                         bool clearOnlySubUnsubEntries )
{
    size_t i = 0;
    MQTTAgentAckInfo_t * pendingAcks;

    assert( pMqttAgentContext != NULL );

    pendingAcks = pMqttAgentContext->pPendingAcks;

    /* Clear all operations pending acknowledgments. */
    for( i = 0; i < MQTT_AGENT_MAX_OUTSTANDING_ACKS; i++ )
    {
        if( pendingAcks[ i ].packetId != MQTT_PACKET_ID_INVALID )
        {
            bool clearEntry = true;

            assert( pendingAcks[ i ].pOriginalCommand != NULL );

            if( clearOnlySubUnsubEntries &&
                ( pendingAcks[ i ].pOriginalCommand->commandType != SUBSCRIBE ) &&
                ( pendingAcks[ i ].pOriginalCommand->commandType != UNSUBSCRIBE ) )
            {
                clearEntry = false;
            }

            if( clearEntry )
            {
                /* Receive failed to indicate network error. */
                concludeCommand( pMqttAgentContext, pendingAcks[ i ].pOriginalCommand, MQTTRecvFailed, NULL );

                /* Now remove it from the list. */
                ( void ) memset( &( pendingAcks[ i ] ), 0x00, sizeof( MQTTAgentAckInfo_t ) );
            }
        }
    }
}

/*-----------------------------------------------------------*/

static bool validateStruct( const MQTTAgentContext_t * pMqttAgentContext,
                            const MQTTAgentCommandInfo_t * pCommandInfo )
{
    bool ret = false;

    if( ( pMqttAgentContext == NULL ) ||
        ( pCommandInfo == NULL ) )
    {
        LogError( ( "Pointer cannot be NULL. pMqttAgentContext=%p, pCommandInfo=%p.",
                    ( void * ) pMqttAgentContext,
                    ( void * ) pCommandInfo ) );
    }
    else if( ( pMqttAgentContext->agentInterface.send == NULL ) ||
             ( pMqttAgentContext->agentInterface.recv == NULL ) ||
             ( pMqttAgentContext->agentInterface.getCommand == NULL ) ||
             ( pMqttAgentContext->agentInterface.releaseCommand == NULL ) ||
             ( pMqttAgentContext->agentInterface.pMsgCtx == NULL ) )
    {
        LogError( ( "pMqttAgentContext must have initialized its messaging interface." ) );
    }
    else
    {
        ret = true;
    }

    return ret;
}

/*-----------------------------------------------------------*/

static bool validateParams( MQTTAgentCommandType_t commandType,
                            const void * pParams )
{
    bool ret = false;
    const MQTTAgentConnectArgs_t * pConnectArgs = NULL;
    const MQTTAgentSubscribeArgs_t * pSubscribeArgs = NULL;

    assert( ( commandType == CONNECT ) || ( commandType == PUBLISH ) ||
            ( commandType == SUBSCRIBE ) || ( commandType == UNSUBSCRIBE ) );

    switch( commandType )
    {
        case CONNECT:
            pConnectArgs = ( const MQTTAgentConnectArgs_t * ) pParams;
            ret = ( ( pConnectArgs != NULL ) &&
                    ( pConnectArgs->pConnectInfo != NULL ) );
            break;

        case SUBSCRIBE:
        case UNSUBSCRIBE:
            pSubscribeArgs = ( const MQTTAgentSubscribeArgs_t * ) pParams;
            ret = ( ( pSubscribeArgs != NULL ) &&
                    ( pSubscribeArgs->pSubscribeInfo != NULL ) &&
                    ( pSubscribeArgs->numSubscriptions != 0U ) );
            break;

        case PUBLISH:
        default:
            /* Publish, does not need to be cast since we do not check it. */
            ret = ( pParams != NULL );
            break;
    }

    return ret;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTTAgent_Init( MQTTAgentContext_t * pMqttAgentContext,
                             const MQTTAgentMessageInterface_t * pMsgInterface,
                             const MQTTFixedBuffer_t * pNetworkBuffer,
                             const TransportInterface_t * pTransportInterface,
                             MQTTGetCurrentTimeFunc_t getCurrentTimeMs,
                             MQTTAgentIncomingPublishCallback_t incomingCallback,
                             void * pIncomingPacketContext )
{
    MQTTStatus_t returnStatus;

    if( ( pMqttAgentContext == NULL ) ||
        ( pMsgInterface == NULL ) ||
        ( pTransportInterface == NULL ) ||
        ( getCurrentTimeMs == NULL ) ||
        ( incomingCallback == NULL ) )
    {
        returnStatus = MQTTBadParameter;
    }
    else if( ( pMsgInterface->pMsgCtx == NULL ) ||
             ( pMsgInterface->send == NULL ) ||
             ( pMsgInterface->recv == NULL ) ||
             ( pMsgInterface->getCommand == NULL ) ||
             ( pMsgInterface->releaseCommand == NULL ) )
    {
        LogError( ( "Invalid parameter: pMsgInterface must set all members." ) );
        returnStatus = MQTTBadParameter;
    }
    else
    {
        ( void ) memset( pMqttAgentContext, 0x00, sizeof( MQTTAgentContext_t ) );

        returnStatus = MQTT_Init( &( pMqttAgentContext->mqttContext ),
                                  pTransportInterface,
                                  getCurrentTimeMs,
                                  mqttEventCallback,
                                  pNetworkBuffer );

        #if ( MQTT_AGENT_USE_QOS_1_2_PUBLISH != 0 )
            {
                if( returnStatus == MQTTSuccess )
                {
                    returnStatus = MQTT_InitStatefulQoS( &( pMqttAgentContext->mqttContext ),
                                                         pOutgoingPublishRecords,
                                                         MQTT_AGENT_MAX_OUTSTANDING_ACKS,
                                                         pIncomingPublishRecords,
                                                         MQTT_AGENT_MAX_OUTSTANDING_ACKS );
                }
            }
        #endif /* if ( MQTT_AGENT_USE_QOS_1_2_PUBLISH != 0 ) */

        if( returnStatus == MQTTSuccess )
        {
            pMqttAgentContext->pIncomingCallback = incomingCallback;
            pMqttAgentContext->pIncomingCallbackContext = pIncomingPacketContext;
            pMqttAgentContext->agentInterface = *pMsgInterface;
        }
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTTAgent_CommandLoop( MQTTAgentContext_t * pMqttAgentContext )
{
    MQTTAgentCommand_t * pCommand;
    MQTTStatus_t operationStatus = MQTTSuccess;
    bool endLoop = false;

    /* The command queue should have been created before this task gets created. */
    if( ( pMqttAgentContext == NULL ) || ( pMqttAgentContext->agentInterface.pMsgCtx == NULL ) )
    {
        operationStatus = MQTTBadParameter;
    }

    /* Loop until an error or we receive a terminate command. */
    while( operationStatus == MQTTSuccess )
    {
        /* Wait for the next command, if any. */
        pCommand = NULL;
        ( void ) pMqttAgentContext->agentInterface.recv(
            pMqttAgentContext->agentInterface.pMsgCtx,
            &( pCommand ),
            MQTT_AGENT_MAX_EVENT_QUEUE_WAIT_TIME
            );
        operationStatus = processCommand( pMqttAgentContext, pCommand, &endLoop );

        if( operationStatus != MQTTSuccess )
        {
            LogError( ( "MQTT operation failed with status %s\n",
                        MQTT_Status_strerror( operationStatus ) ) );
        }

        /* Terminate the loop on disconnects, errors, or the termination command. */
        if( endLoop )
        {
            break;
        }
    }

    return operationStatus;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTTAgent_ResumeSession( MQTTAgentContext_t * pMqttAgentContext,
                                      bool sessionPresent )
{
    MQTTStatus_t statusResult = MQTTSuccess;

    /* If the packet ID is zero then the MQTT context has not been initialized as 0
     * is the initial value but not a valid packet ID. */
    if( ( pMqttAgentContext != NULL ) &&
        ( pMqttAgentContext->mqttContext.nextPacketId != MQTT_PACKET_ID_INVALID ) )
    {
        /* Resend publishes if session is present. NOTE: It's possible that some
         * of the operations that were in progress during the network interruption
         * were subscribes. In that case, we would want to mark those operations
         * as completing with error and remove them from the list of operations, so
         * that the calling task can try subscribing again. */
        if( sessionPresent )
        {
            /* The session has resumed, so clear any SUBSCRIBE/UNSUBSCRIBE operations
             * that were pending acknowledgments in the previous connection. */
            clearPendingAcknowledgments( pMqttAgentContext, true );

            statusResult = resendPublishes( pMqttAgentContext );
        }

        /* If we wanted to resume a session but none existed with the broker, we
         * should mark all in progress operations as errors so that the tasks that
         * created them can try again. */
        else
        {
            /* We have a clean session, so clear all operations pending acknowledgments. */
            clearPendingAcknowledgments( pMqttAgentContext, false );
        }
    }
    else
    {
        statusResult = MQTTBadParameter;
    }

    return statusResult;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTTAgent_CancelAll( MQTTAgentContext_t * pMqttAgentContext )
{
    MQTTStatus_t statusReturn = MQTTSuccess;
    MQTTAgentCommand_t * pReceivedCommand = NULL;
    bool commandWasReceived = false;
    MQTTAgentAckInfo_t * pendingAcks;
    size_t i;

    if( ( pMqttAgentContext == NULL ) || ( pMqttAgentContext->agentInterface.pMsgCtx == NULL ) )
    {
        statusReturn = MQTTBadParameter;
    }
    else
    {
        /* Cancel all operations waiting in the queue. */
        do
        {
            pReceivedCommand = NULL;
            commandWasReceived = pMqttAgentContext->agentInterface.recv(
                pMqttAgentContext->agentInterface.pMsgCtx,
                &( pReceivedCommand ),
                0U );

            if( pReceivedCommand != NULL )
            {
                concludeCommand( pMqttAgentContext, pReceivedCommand, MQTTRecvFailed, NULL );
            }
        } while( commandWasReceived );

        pendingAcks = pMqttAgentContext->pPendingAcks;

        /* Cancel any operations awaiting an acknowledgment. */
        for( i = 0; i < MQTT_AGENT_MAX_OUTSTANDING_ACKS; i++ )
        {
            if( pendingAcks[ i ].packetId != MQTT_PACKET_ID_INVALID )
            {
                concludeCommand( pMqttAgentContext, pendingAcks[ i ].pOriginalCommand, MQTTRecvFailed, NULL );

                /* Now remove it from the list. */
                ( void ) memset( &( pendingAcks[ i ] ), 0x00, sizeof( MQTTAgentAckInfo_t ) );
            }
        }
    }

    return statusReturn;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTTAgent_Subscribe( const MQTTAgentContext_t * pMqttAgentContext,
                                  MQTTAgentSubscribeArgs_t * pSubscriptionArgs,
                                  const MQTTAgentCommandInfo_t * pCommandInfo )
{
    MQTTStatus_t statusReturn = MQTTBadParameter;
    bool paramsValid = false;

    paramsValid = validateStruct( pMqttAgentContext, pCommandInfo ) &&
                  validateParams( SUBSCRIBE, pSubscriptionArgs );

    if( paramsValid )
    {
        statusReturn = createAndAddCommand( SUBSCRIBE,                                 /* commandType */
                                            pMqttAgentContext,                         /* mqttContextHandle */
                                            pSubscriptionArgs,                         /* pMqttInfoParam */
                                            pCommandInfo->cmdCompleteCallback,         /* commandCompleteCallback */
                                            pCommandInfo->pCmdCompleteCallbackContext, /* pCommandCompleteCallbackContext */
                                            pCommandInfo->blockTimeMs );
    }

    return statusReturn;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTTAgent_Unsubscribe( const MQTTAgentContext_t * pMqttAgentContext,
                                    MQTTAgentSubscribeArgs_t * pSubscriptionArgs,
                                    const MQTTAgentCommandInfo_t * pCommandInfo )
{
    MQTTStatus_t statusReturn = MQTTBadParameter;
    bool paramsValid = false;

    paramsValid = validateStruct( pMqttAgentContext, pCommandInfo ) &&
                  validateParams( UNSUBSCRIBE, pSubscriptionArgs );

    if( paramsValid )
    {
        statusReturn = createAndAddCommand( UNSUBSCRIBE,                               /* commandType */
                                            pMqttAgentContext,                         /* mqttContextHandle */
                                            pSubscriptionArgs,                         /* pMqttInfoParam */
                                            pCommandInfo->cmdCompleteCallback,         /* commandCompleteCallback */
                                            pCommandInfo->pCmdCompleteCallbackContext, /* pCommandCompleteCallbackContext */
                                            pCommandInfo->blockTimeMs );
    }

    return statusReturn;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTTAgent_Publish( const MQTTAgentContext_t * pMqttAgentContext,
                                MQTTPublishInfo_t * pPublishInfo,
                                const MQTTAgentCommandInfo_t * pCommandInfo )
{
    MQTTStatus_t statusReturn = MQTTBadParameter;
    bool paramsValid = false;

    paramsValid = validateStruct( pMqttAgentContext, pCommandInfo ) &&
                  validateParams( PUBLISH, pPublishInfo );

    if( paramsValid )
    {
        statusReturn = createAndAddCommand( PUBLISH,                                   /* commandType */
                                            pMqttAgentContext,                         /* mqttContextHandle */
                                            pPublishInfo,                              /* pMqttInfoParam */
                                            pCommandInfo->cmdCompleteCallback,         /* commandCompleteCallback */
                                            pCommandInfo->pCmdCompleteCallbackContext, /* pCommandCompleteCallbackContext */
                                            pCommandInfo->blockTimeMs );
    }

    return statusReturn;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTTAgent_ProcessLoop( const MQTTAgentContext_t * pMqttAgentContext,
                                    const MQTTAgentCommandInfo_t * pCommandInfo )
{
    MQTTStatus_t statusReturn = MQTTBadParameter;
    bool paramsValid = false;

    paramsValid = validateStruct( pMqttAgentContext, pCommandInfo );

    if( paramsValid )
    {
        statusReturn = createAndAddCommand( PROCESSLOOP,                               /* commandType */
                                            pMqttAgentContext,                         /* mqttContextHandle */
                                            NULL,                                      /* pMqttInfoParam */
                                            pCommandInfo->cmdCompleteCallback,         /* commandCompleteCallback */
                                            pCommandInfo->pCmdCompleteCallbackContext, /* pCommandCompleteCallbackContext */
                                            pCommandInfo->blockTimeMs );
    }

    return statusReturn;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTTAgent_Connect( const MQTTAgentContext_t * pMqttAgentContext,
                                MQTTAgentConnectArgs_t * pConnectArgs,
                                const MQTTAgentCommandInfo_t * pCommandInfo )
{
    MQTTStatus_t statusReturn = MQTTBadParameter;
    bool paramsValid = false;

    paramsValid = validateStruct( pMqttAgentContext, pCommandInfo ) &&
                  validateParams( CONNECT, pConnectArgs );

    if( paramsValid )
    {
        statusReturn = createAndAddCommand( CONNECT,
                                            pMqttAgentContext,
                                            pConnectArgs,
                                            pCommandInfo->cmdCompleteCallback,
                                            pCommandInfo->pCmdCompleteCallbackContext,
                                            pCommandInfo->blockTimeMs );
    }

    return statusReturn;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTTAgent_Disconnect( const MQTTAgentContext_t * pMqttAgentContext,
                                   const MQTTAgentCommandInfo_t * pCommandInfo )
{
    MQTTStatus_t statusReturn = MQTTBadParameter;
    bool paramsValid = false;

    paramsValid = validateStruct( pMqttAgentContext, pCommandInfo );

    if( paramsValid )
    {
        statusReturn = createAndAddCommand( DISCONNECT,                                /* commandType */
                                            pMqttAgentContext,                         /* mqttContextHandle */
                                            NULL,                                      /* pMqttInfoParam */
                                            pCommandInfo->cmdCompleteCallback,         /* commandCompleteCallback */
                                            pCommandInfo->pCmdCompleteCallbackContext, /* pCommandCompleteCallbackContext */
                                            pCommandInfo->blockTimeMs );
    }

    return statusReturn;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTTAgent_Ping( const MQTTAgentContext_t * pMqttAgentContext,
                             const MQTTAgentCommandInfo_t * pCommandInfo )
{
    MQTTStatus_t statusReturn = MQTTBadParameter;
    bool paramsValid = false;

    paramsValid = validateStruct( pMqttAgentContext, pCommandInfo );

    if( paramsValid )
    {
        statusReturn = createAndAddCommand( PING,                                      /* commandType */
                                            pMqttAgentContext,                         /* mqttContextHandle */
                                            NULL,                                      /* pMqttInfoParam */
                                            pCommandInfo->cmdCompleteCallback,         /* commandCompleteCallback */
                                            pCommandInfo->pCmdCompleteCallbackContext, /* pCommandCompleteCallbackContext */
                                            pCommandInfo->blockTimeMs );
    }

    return statusReturn;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTTAgent_Terminate( const MQTTAgentContext_t * pMqttAgentContext,
                                  const MQTTAgentCommandInfo_t * pCommandInfo )
{
    MQTTStatus_t statusReturn = MQTTBadParameter;
    bool paramsValid = false;

    paramsValid = validateStruct( pMqttAgentContext, pCommandInfo );

    if( paramsValid )
    {
        statusReturn = createAndAddCommand( TERMINATE,
                                            pMqttAgentContext,
                                            NULL,
                                            pCommandInfo->cmdCompleteCallback,
                                            pCommandInfo->pCmdCompleteCallbackContext,
                                            pCommandInfo->blockTimeMs );
    }

    return statusReturn;
}

/*-----------------------------------------------------------*/
