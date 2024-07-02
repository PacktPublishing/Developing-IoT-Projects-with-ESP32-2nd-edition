# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: MIT-0

HARNESS_FILE=JSON_Iterate_harness
PROOF_UID=JSON_Iterate

# These values were experimentally chosen to provide 100% coverage
# without tripping unwinding assertions and without exhausting memory.
CBMC_MAX_BUFSIZE=7

UNWINDSET += nextValue.0:$(CBMC_MAX_BUFSIZE)
UNWINDSET += nextKeyValuePair.0:$(CBMC_MAX_BUFSIZE)


PROOF_SOURCES += $(PROOF_STUB)/skipGeneric.c
PROOF_SOURCES += $(PROOF_STUB)/skipAnyScalar.c
PROOF_SOURCES += $(PROOF_STUB)/skipCollection.c
PROOF_SOURCES += $(PROOF_STUB)/skipDigits.c
PROOF_SOURCES += $(PROOF_STUB)/skipSpace.c
PROOF_SOURCES += $(PROOF_STUB)/skipSpaceAndComma.c
PROOF_SOURCES += $(PROOF_STUB)/skipString.c

include ../Makefile-json.common

# Substitution command to pass to sed for patching core_json.c. The
# characters " and # must be escaped with backslash.
CORE_JSON_SED_EXPR = 1s/^/\#include \"core_json_annex.h\" /; s/^static //; s/(bool|void|JSONStatus_t) skip(AnyScalar|Collection|Digits|Space|SpaceAndComma|String)\b/&_/
