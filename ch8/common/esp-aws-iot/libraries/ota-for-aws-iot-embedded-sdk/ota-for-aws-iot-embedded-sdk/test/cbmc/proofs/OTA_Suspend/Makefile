# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: MIT-0

HARNESS_ENTRY = OTA_Suspend_harness
HARNESS_FILE = $(HARNESS_ENTRY)

# This should be a unique identifier for this proof, and will appear on the
# Litani dashboard. It can be human-readable and contain spaces if you wish.
PROOF_UID = OTA_Suspend_harness

DEFINES += -Dstatic=""

INCLUDES += -I$(SRCDIR)/source/dependency/coreJSON/source/include/
INCLUDES += -I$(SRCDIR)/test/cbmc/include/

PROOF_SOURCES += $(PROOFDIR)/$(HARNESS_FILE).c

PROJECT_SOURCES += $(SRCDIR)/source/ota.c

REMOVE_FUNCTION_BODY += OTA_SignalEvent
RESTRICT_FUNCTION_POINTER += OTA_Suspend.function_pointer_call.1/timerStop

# If this proof is found to consume huge amounts of RAM, you can set the
# EXPENSIVE variable. With new enough versions of the proof tools, this will
# restrict the number of EXPENSIVE CBMC jobs running at once. See the
# documentation in Makefile.common under the "Job Pools" heading for details.
# EXPENSIVE = true

include ../Makefile.common
