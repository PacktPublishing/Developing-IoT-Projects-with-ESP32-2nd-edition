HARNESS_ENTRY = processDataHandler_harness
HARNESS_FILE = $(HARNESS_ENTRY)

# This should be a unique identifier for this proof, and will appear on the
# Litani dashboard. It can be human-readable and contain spaces if you wish.
PROOF_UID = processDataHandler

DEFINES += -Dstatic=""

INCLUDES += -I$(SRCDIR)/source/dependency/coreJSON/source/include/
INCLUDES += -I$(SRCDIR)/source/

PROOF_SOURCES += $(PROOFDIR)/$(HARNESS_FILE).c
PROJECT_SOURCES += $(SRCDIR)/source/ota.c
PROJECT_SOURCES += $(SRCDIR)/source/ota_interface.c

UNWINDSET += strlen.0:74

REMOVE_FUNCTION_BODY += ingestDataBlock
REMOVE_FUNCTION_BODY += dataHandlerCleanup
REMOVE_FUNCTION_BODY += OTA_SignalEvent

RESTRICT_FUNCTION_POINTER += processDataHandler.function_pointer_call.1/updateStatus 
RESTRICT_FUNCTION_POINTER += processDataHandler.function_pointer_call.2/setImageState
RESTRICT_FUNCTION_POINTER += processDataHandler.function_pointer_call.3/updateStatus 
RESTRICT_FUNCTION_POINTER += processDataHandler.function_pointer_call.4/updateStatus 
RESTRICT_FUNCTION_POINTER += processDataHandler.function_pointer_call.5/start 
RESTRICT_FUNCTION_POINTER += callOtaCallback.function_pointer_call.1/otaAppCallback

# If this proof is found to consume huge amounts of RAM, you can set the
# EXPENSIVE variable. With new enough versions of the proof tools, this will
# restrict the number of EXPENSIVE CBMC jobs running at once. See the
# documentation in Makefile.common under the "Job Pools" heading for details.
# EXPENSIVE = true

include ../Makefile.common
