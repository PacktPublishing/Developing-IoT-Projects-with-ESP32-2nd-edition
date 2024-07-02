# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: MIT-0

HARNESS_ENTRY = harness
HARNESS_FILE = MQTTAgent_CommandLoop_harness

# This should be a unique identifier for this proof, and will appear on the
# Litani dashboard. It can be human-readable and contain spaces if you wish.
PROOF_UID = MQTTAgent_CommandLoop

# MQTT_AGENT_MAX_OUTSTANDING_ACKS set the maximum number of acknowledgments
# that can be outstanding at any one time. A small number 2 will be enough
# for proving the memory safety and making the proofs run faster.
MQTT_AGENT_MAX_OUTSTANDING_ACKS=2

# Bound for loop unwinding for the loops trying to read and write into the
# outstanding acks array. The size of the array is determined by
# MQTT_AGENT_MAX_OUTSTANDING_ACKS. The max bound will be one more than
# array size for the proofs.
MAX_BOUND_FOR_PENDING_ACK_LOOPS=$(shell expr $(MQTT_AGENT_MAX_OUTSTANDING_ACKS) + 1 )

# Bound for loop unwinding for the main loop in MQTTAgent_CommandLoop. Unwinding
# the loop 3 times will be enough for proving memory safety.
MAX_BOUND_FOR_COMMAND_LOOP=3

# Bound for loop unwinding for loop in processCommand function. Unwinding
# the loop 2 times will be enough for proving memory safety.
MAX_BOUND_FOR_PROCESS_COMMAND_LOOP=2

DEFINES += -DMQTT_AGENT_MAX_OUTSTANDING_ACKS=$(MQTT_AGENT_MAX_OUTSTANDING_ACKS)

INCLUDES +=

REMOVE_FUNCTION_BODY +=

UNWINDSET += MQTTAgent_CommandLoop.0:$(MAX_BOUND_FOR_COMMAND_LOOP)
UNWINDSET += __CPROVER_file_local_core_mqtt_agent_c_addAwaitingOperation.0:$(MAX_BOUND_FOR_PENDING_ACK_LOOPS)
UNWINDSET += __CPROVER_file_local_core_mqtt_agent_c_getAwaitingOperation.0:$(MAX_BOUND_FOR_PENDING_ACK_LOOPS)
UNWINDSET += __CPROVER_file_local_core_mqtt_agent_c_processCommand.0:$(MAX_BOUND_FOR_PROCESS_COMMAND_LOOP)

PROOF_SOURCES += $(PROOFDIR)/$(HARNESS_FILE).c
PROOF_SOURCES += $(SRCDIR)/test/cbmc/sources/mqtt_agent_cbmc_state.c
PROOF_SOURCES += $(SRCDIR)/test/cbmc/stubs/network_interface_stubs.c
PROOF_SOURCES += $(SRCDIR)/test/cbmc/stubs/incoming_publish_callback_stub.c
PROOF_SOURCES += $(SRCDIR)/test/cbmc/stubs/get_time_stub.c
PROOF_SOURCES += $(SRCDIR)/test/cbmc/stubs/agent_command_pool_stubs.c
PROOF_SOURCES += $(SRCDIR)/test/cbmc/stubs/agent_message_stubs.c
PROOF_SOURCES += $(SRCDIR)/test/cbmc/stubs/agent_command_functions_stub.c
PROOF_SOURCES += $(SRCDIR)/test/cbmc/stubs/core_mqtt_stubs.c

PROJECT_SOURCES += $(SRCDIR)/source/core_mqtt_agent.c

include ../Makefile.common
