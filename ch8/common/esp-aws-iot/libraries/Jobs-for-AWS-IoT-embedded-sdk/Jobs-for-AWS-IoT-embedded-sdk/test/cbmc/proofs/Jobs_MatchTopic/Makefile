# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: MIT-0

HARNESS_FILE=Jobs_MatchTopic_harness

# Limit thing name and job id maximums - values arbitrarily chosen
# to provide 100% coverage and to reduce unwindings
THINGNAME_MAX_LENGTH=6
EXCEED_THINGNAME_MAX_LENGTH=7
JOBID_MAX_LENGTH=4
EXCEED_JOBID_MAX_LENGTH=5

# Use the largest of the above
UNWINDSET += isValidID.0:$(EXCEED_THINGNAME_MAX_LENGTH)

# This size holds the longest topic, including thing name and job id
CBMC_MAX_BUFSIZE=50

# Provide sufficient unwindings to iterate through the API enums
APIS_WITHOUT_JOBID=7
APIS_WITH_JOBID=6

REMOVE_FUNCTION_BODY +=
UNWINDSET += matchApi.0:$(APIS_WITHOUT_JOBID)
UNWINDSET += matchIdApi.0:$(CBMC_MAX_BUFSIZE)
UNWINDSET += matchIdApi.1:$(APIS_WITH_JOBID)

# Use a stub in place of the original function.
PROOF_SOURCES += $(PROOF_STUB)/strnEq.c
# Rename original function (used in Makefile-jobs.common)
SED_EXPR = s/JobsStatus_t strnEq\b/&_/

include ../Makefile-jobs.common
PROOF_UID=Jobs_MatchTopic
