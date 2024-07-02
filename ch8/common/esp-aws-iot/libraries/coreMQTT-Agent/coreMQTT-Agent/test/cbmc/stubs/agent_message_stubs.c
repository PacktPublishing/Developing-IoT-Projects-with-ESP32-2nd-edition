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
 * @file agent_message_stubs.h
 * @brief Stub functions to interact with queues.
 */

#include "core_mqtt_agent.h"
#include "agent_message_stubs.h"

static void commandCompleteCallbackStub( void * pCmdCallbackContext,
                                         MQTTAgentReturnInfo_t * pReturnInfo )
{
    __CPROVER_assert( pReturnInfo != NULL,
                      "Command complete return info is not NULL." );
}

static MQTTAgentCommand_t * allocateCommand()
{
    MQTTAgentSubscribeArgs_t * pSubscribeArgs;
    MQTTPublishInfo_t * pPublishInfo;
    static bool terminate = false;

    MQTTAgentCommand_t * command = malloc( sizeof( MQTTAgentCommand_t ) );

    /* Second command always is TERMINATE to keep the MQTTAgent_CommandLoop unwind bound. */
    if( terminate == true )
    {
        __CPROVER_assume( command != NULL );
        __CPROVER_assume( command->commandType == TERMINATE );
    }

    if( command != NULL )
    {
        __CPROVER_assume( command->commandType >= NONE && command->commandType < NUM_COMMANDS );

        if( ( command->commandType == SUBSCRIBE ) || ( command->commandType == UNSUBSCRIBE ) )
        {
            pSubscribeArgs = malloc( sizeof( MQTTAgentSubscribeArgs_t ) );
            command->pArgs = ( void * ) pSubscribeArgs;
        }
        else if( command->commandType == PUBLISH )
        {
            pPublishInfo = malloc( sizeof( MQTTPublishInfo_t ) );
            command->pArgs = ( void * ) pPublishInfo;
        }
        else
        {
            /* Empty else. */
        }

        __CPROVER_assume( command->pCommandCompleteCallback == commandCompleteCallbackStub );
    }

    terminate = true;
    return command;
}

bool AgentMessageSendStub( MQTTAgentMessageContext_t * pMsgCtx,
                           const void * pData,
                           uint32_t blockTimeMs )
{
    /* For the proofs, returning a non deterministic boolean value
     * will be good enough. */
    return nondet_bool();
}

bool AgentMessageRecvStub( MQTTAgentMessageContext_t * pMsgCtx,
                           void * pBuffer,
                           uint32_t blockTimeMs )
{
    MQTTAgentCommand_t * command;
    bool returnStatus;

    __CPROVER_assert( pBuffer != NULL,
                      "Command buffer is not NULL." );

    command = allocateCommand();

    if( ( command != NULL ) && ( command->commandType == TERMINATE ) )
    {
        returnStatus = false;
    }

    *( ( MQTTAgentCommand_t ** ) pBuffer ) = command;

    return returnStatus;
}
