
HARNESS_ENTRY = parseJSONbyModel_harness
HARNESS_FILE = $(HARNESS_ENTRY)

# This should be a unique identifier for this proof, and will appear on the
# Litani dashboard. It can be human-readable and contain spaces if you wish.
PROOF_UID = parseJSONbyModel

DEFINES += -Dstatic=""
DEFINES += -DOTA_NUM_PARAMS=30
DEFINES += -DOTA_JSON_SRC_KEY_SIZE=44

INCLUDES += -I$(SRCDIR)/source/dependency/coreJSON/source/include/

UNWINDSET += strlen.0:45
UNWINDSET += parseJSONbyModel.0:30
UNWINDSET += parseJSONbyModel_harness.0:30
UNWINDSET += parseJSONbyModel_harness.1:30

PROOF_SOURCES += $(PROOFDIR)/$(HARNESS_FILE).c
PROJECT_SOURCES += $(SRCDIR)/source/ota.c

# If this proof is found to consume huge amounts of RAM, you can set the
# EXPENSIVE variable. With new enough versions of the proof tools, this will
# restrict the number of EXPENSIVE CBMC jobs running at once. See the
# documentation in Makefile.common under the "Job Pools" heading for details.
# EXPENSIVE = true

include ../Makefile.common
