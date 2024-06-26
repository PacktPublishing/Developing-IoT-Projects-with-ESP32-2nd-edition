
HARNESS_ENTRY = agentShutdownCleanup_harness
HARNESS_FILE = $(HARNESS_ENTRY)

# This should be a unique identifier for this proof, and will appear on the
# Litani dashboard. It can be human-readable and contain spaces if you wish.
PROOF_UID = agentShutdownCleanup

DEFINES += -Dstatic=""

INCLUDES += -I$(SRCDIR)/source/dependency/coreJSON/source/include/
INCLUDES += -I$(SRCDIR)/test/cbmc/include

PROOF_SOURCES += $(PROOFDIR)/$(HARNESS_FILE).c
PROOF_SOURCES += $(SRCDIR)/test/cbmc/source/stubs.c

PROJECT_SOURCES += $(SRCDIR)/source/ota.c

REMOVE_FUNCTION_BODY += otaClose

# The upper bound on the for loop in agentShutdownCLeanup is set by OTA_MAX_FILES.
UNWINDSET += agentShutdownCleanup.0:2

RESTRICT_FUNCTION_POINTER += agentShutdownCleanup.function_pointer_call.1/stopTimerStub
RESTRICT_FUNCTION_POINTER += agentShutdownCleanup.function_pointer_call.2/deleteTimerStub
RESTRICT_FUNCTION_POINTER += agentShutdownCleanup.function_pointer_call.3/stopTimerStub
RESTRICT_FUNCTION_POINTER += agentShutdownCleanup.function_pointer_call.4/deleteTimerStub
RESTRICT_FUNCTION_POINTER += agentShutdownCleanup.function_pointer_call.5/cleanupStub
RESTRICT_FUNCTION_POINTER += agentShutdownCleanup.function_pointer_call.6/cleanupStub

# If this proof is found to consume huge amounts of RAM, you can set the
# EXPENSIVE variable. With new enough versions of the proof tools, this will
# restrict the number of EXPENSIVE CBMC jobs running at once. See the
# documentation in Makefile.common under the "Job Pools" heading for details.
# EXPENSIVE = true

include ../Makefile.common
