
HARNESS_ENTRY = processValidFileContext_harness
HARNESS_FILE = $(HARNESS_ENTRY)

# This should be a unique identifier for this proof, and will appear on the
# Litani dashboard. It can be human-readable and contain spaces if you wish.
PROOF_UID = processValidFileContext

DEFINES += -Dstatic=""

INCLUDES += -I$(SRCDIR)/source/dependency/coreJSON/source/include/
INCLUDES += -I$(SRCDIR)/test/cbmc/include

PROOF_SOURCES += $(PROOFDIR)/$(HARNESS_FILE).c
PROOF_SOURCES += $(SRCDIR)/test/cbmc/source/stubs.c

PROJECT_SOURCES += $(SRCDIR)/source/ota.c
PROJECT_SOURCES += $(SRCDIR)/source/ota_interface.c

REMOVE_FUNCTION_BODY += setImageStateWithReason

RESTRICT_FUNCTION_POINTER += processValidFileContext.function_pointer_call.1/resetPalStub
RESTRICT_FUNCTION_POINTER += platformInSelftest.function_pointer_call.1/getPlatformImageStateStub
RESTRICT_FUNCTION_POINTER += OTA_SignalEvent.function_pointer_call.1/sendEventStub

# If this proof is found to consume huge amounts of RAM, you can set the
# EXPENSIVE variable. With new enough versions of the proof tools, this will
# restrict the number of EXPENSIVE CBMC jobs running at once. See the
# documentation in Makefile.common under the "Job Pools" heading for details.
# EXPENSIVE = true

include ../Makefile.common
