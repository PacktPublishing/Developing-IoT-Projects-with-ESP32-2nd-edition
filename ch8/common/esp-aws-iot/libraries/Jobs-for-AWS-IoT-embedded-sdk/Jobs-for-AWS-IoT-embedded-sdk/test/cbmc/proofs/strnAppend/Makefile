# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: MIT-0

HARNESS_FILE=strnAppend_harness

# This value was experimentally chosen to provide 100% coverage
# without tripping unwinding assertions and without exhausting memory.
CBMC_MAX_BUFSIZE=10

REMOVE_FUNCTION_BODY +=
UNWINDSET += strnAppend.0:$(CBMC_MAX_BUFSIZE)

include ../Makefile-jobs.common
PROOF_UID=strnAppend
