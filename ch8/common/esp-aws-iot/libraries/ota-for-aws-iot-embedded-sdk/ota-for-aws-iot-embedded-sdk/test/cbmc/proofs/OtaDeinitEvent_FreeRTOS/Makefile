HARNESS_ENTRY = OtaDeinitEvent_FreeRTOS_harness
HARNESS_FILE = $(HARNESS_ENTRY)

# This should be a unique identifier for this proof, and will appear on the
# Litani dashboard. It can be human-readable and contain spaces if you wish.
PROOF_UID = OtaDeinitEvent_FreeRTOS_harness

INCLUDES += -I$(SRCDIR)/source/portable/os/
INCLUDES += -I$(SRCDIR)/test/cbmc/FreeRTOS-Kernel/include/
INCLUDES += -I$(SRCDIR)/test/cbmc/include/
INCLUDES += -I$(SRCDIR)/test/cbmc/FreeRTOS-Kernel/portable/CCS/ARM_CM3/

PROOF_SOURCES += $(PROOFDIR)/$(HARNESS_FILE).c

PROJECT_SOURCES += $(SRCDIR)/source/portable/os/ota_os_freertos.c

NONDET_STATIC += "--nondet-static"

REMOVE_FUNCTION_BODIES += vQueueDelete

# If this proof is found to consume huge amounts of RAM, you can set the
# EXPENSIVE variable. With new enough versions of the proof tools, this will
# restrict the number of EXPENSIVE CBMC jobs running at once. See the
# documentation in Makefile.common under the "Job Pools" heading for details.
# EXPENSIVE = true

include ../Makefile.common
