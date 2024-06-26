HARNESS_ENTRY = OTA_Init_harness
HARNESS_FILE = $(HARNESS_ENTRY)

# This should be a unique identifier for this proof, and will appear on the
# Litani dashboard. It can be human-readable and contain spaces if you wish.
PROOF_UID = OTA_Init

INCLUDES += -I$(SRCDIR)/source/dependency/coreJSON/source/include/
INCLUDES += -I$(SRCDIR)/source/

PROOF_SOURCES += $(PROOFDIR)/$(HARNESS_FILE).c
PROJECT_SOURCES += $(SRCDIR)/source/ota.c

NONDET_STATIC += "--nondet-static"

UNWINDSET += strlen.0:66

REMOVE_FUNCTION_BODY += setControlInterface
REMOVE_FUNCTION_BODY += __CPROVER_file_local_ota_c_initializeAppBuffers
REMOVE_FUNCTION_BODY += __CPROVER_file_local_ota_c_initializeLocalBuffers
REMOVE_FUNCTION_BODY += __CPROVER_file_local_ota_c_resetEventQueue

RESTRICT_FUNCTION_POINTER += OTA_Init.function_pointer_call.1/init 

# If this proof is found to consume huge amounts of RAM, you can set the
# EXPENSIVE variable. With new enough versions of the proof tools, this will
# restrict the number of EXPENSIVE CBMC jobs running at once. See the
# documentation in Makefile.common under the "Job Pools" heading for details.
# EXPENSIVE = true

include ../Makefile.common
