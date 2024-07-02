# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: MIT-0

HARNESS_FILE=skipNumber_harness
PROOF_UID=skipNumber

# This value was experimentally chosen to provide 100% coverage
# without tripping unwinding assertions and without exhausting memory.
CBMC_MAX_BUFSIZE=12

UNWINDSET += skipDecimals.0:$(CBMC_MAX_BUFSIZE)
UNWINDSET += skipDigits.0:$(CBMC_MAX_BUFSIZE)
UNWINDSET += skipExponent.0:$(CBMC_MAX_BUFSIZE)
UNWINDSET += skipNumber.0:$(CBMC_MAX_BUFSIZE)

include ../Makefile-json.common

# Substitution command to pass to sed for patching core_json.c. The
# characters " and # must be escaped with backslash.
CORE_JSON_SED_EXPR = s/^static //
