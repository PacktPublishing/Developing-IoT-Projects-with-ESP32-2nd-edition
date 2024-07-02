# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: MIT-0

HARNESS_FILE=JSON_Search_harness
PROOF_UID=JSON_Search

# These values were experimentally chosen to provide 100% coverage
# without tripping unwinding assertions and without exhausting memory.
CBMC_MAX_BUFSIZE=7
CBMC_MAX_QUERYKEYLENGTH=6

REMOVE_FUNCTION_BODY += strnEq
UNWINDSET += JSON_SearchT.0:$(CBMC_MAX_QUERYKEYLENGTH)
UNWINDSET += JSON_SearchT.1:$(CBMC_MAX_QUERYKEYLENGTH)
UNWINDSET += arraySearch.0:$(CBMC_MAX_BUFSIZE)
UNWINDSET += multiSearch.0:$(CBMC_MAX_BUFSIZE)
UNWINDSET += nextValue.0:$(CBMC_MAX_BUFSIZE)
UNWINDSET += nextKeyValuePair.0:$(CBMC_MAX_BUFSIZE)
UNWINDSET += objectSearch.0:$(CBMC_MAX_BUFSIZE)
UNWINDSET += skipQueryPart.0:$(CBMC_MAX_QUERYKEYLENGTH)


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
