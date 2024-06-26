# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: MIT-0

HARNESS_ENTRY = harness
HARNESS_FILE = MQTTAgent_Subscribe_harness

# This should be a unique identifier for this proof, and will appear on the
# Litani dashboard. It can be human-readable and contain spaces if you wish.
PROOF_UID = MQTTAgent_Subscribe

DEFINES +=
INCLUDES +=

REMOVE_FUNCTION_BODY +=
UNWINDSET +=

PROOF_SOURCES += $(PROOFDIR)/$(HARNESS_FILE).c
PROOF_SOURCES += $(SRCDIR)/test/cbmc/sources/mqtt_agent_cbmc_state.c
PROOF_SOURCES += $(SRCDIR)/test/cbmc/stubs/network_interface_stubs.c
PROOF_SOURCES += $(SRCDIR)/test/cbmc/stubs/incoming_publish_callback_stub.c
PROOF_SOURCES += $(SRCDIR)/test/cbmc/stubs/get_time_stub.c
PROOF_SOURCES += $(SRCDIR)/test/cbmc/stubs/agent_command_pool_stubs.c
PROOF_SOURCES += $(SRCDIR)/test/cbmc/stubs/agent_message_stubs.c

PROJECT_SOURCES += $(SRCDIR)/source/core_mqtt_agent.c
PROJECT_SOURCES += $(SRCDIR)/source/dependency/coreMQTT/source/core_mqtt.c
PROJECT_SOURCES += $(SRCDIR)/source/dependency/coreMQTT/source/core_mqtt_serializer.c

include ../Makefile.common
