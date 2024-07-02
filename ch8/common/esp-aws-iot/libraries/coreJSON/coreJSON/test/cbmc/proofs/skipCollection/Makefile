# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: MIT-0

HARNESS_FILE=skipCollection_harness
PROOF_UID=skipCollection

# This value was experimentally chosen to provide 100% coverage
# without tripping unwinding assertions and without exhausting memory.
CBMC_MAX_BUFSIZE=8

DEFINES += -DJSON_MAX_DEPTH="( $(CBMC_MAX_BUFSIZE) - 2 )"

REMOVE_FUNCTION_BODY += strnEq
UNWINDSET += skipCollection.0:$(CBMC_MAX_BUFSIZE)
UNWINDSET += skipArrayScalars.0:$(CBMC_MAX_BUFSIZE)
UNWINDSET += skipObjectScalars.0:$(CBMC_MAX_BUFSIZE)

PROOF_SOURCES += $(PROOF_STUB)/skipGeneric.c
PROOF_SOURCES += $(PROOF_STUB)/skipAnyLiteral.c
PROOF_SOURCES += $(PROOF_STUB)/skipNumber.c
PROOF_SOURCES += $(PROOF_STUB)/skipSpace.c
PROOF_SOURCES += $(PROOF_STUB)/skipSpaceAndComma.c
PROOF_SOURCES += $(PROOF_STUB)/skipString.c

include ../Makefile-json.common

# Substitution command to pass to sed for patching core_json.c. The
# characters " and # must be escaped with backslash.
CORE_JSON_SED_EXPR = 1s/^/\#include \"core_json_annex.h\" /; s/^static //; s/(bool|void) skip(AnyLiteral|Number|Space|SpaceAndComma|String)\b/&_/
