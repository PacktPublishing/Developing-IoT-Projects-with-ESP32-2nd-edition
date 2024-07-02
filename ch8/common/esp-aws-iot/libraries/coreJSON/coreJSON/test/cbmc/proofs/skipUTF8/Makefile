# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: MIT-0

HARNESS_FILE=skipUTF8_harness
PROOF_UID=skipUTF8

# This value was experimentally chosen to provide 100% coverage
# without tripping unwinding assertions and without exhausting memory.
CBMC_MAX_BUFSIZE=10

UNWINDSET += countHighBits.0:9
UNWINDSET += skipUTF8.0:$(CBMC_MAX_BUFSIZE)
UNWINDSET += skipUTF8MultiByte.0:$(CBMC_MAX_BUFSIZE)

include ../Makefile-json.common

# Substitution command to pass to sed for patching core_json.c. The
# characters " and # must be escaped with backslash.
CORE_JSON_SED_EXPR = s/^static //
