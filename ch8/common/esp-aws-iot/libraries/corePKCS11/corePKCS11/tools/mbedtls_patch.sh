#!/bin/sh

if [ $# -lt 2 ]; then
    echo "Usage: mbedtls_patch.sh <MBEDTLS_SRC_DIR> <PATCH_1> [<PATCH_2>].."
    exit 1
fi

MBEDTLS_DIR="${1}"

shift

PATCHES="${1}"

shift

while [ $# -gt 0 ]; do
    PATCHES="${PATCHES} ${1}"
    shift
done

for patch in ${PATCHES}; do
    if git -C "${MBEDTLS_DIR}" apply --check --quiet --reverse "${patch}"; then
        echo "patch: $(basename "${patch}") already applied"
    else
        echo "patch: applying $(basename "${patch}")"
        git -C "${MBEDTLS_DIR}" apply "${patch}"
    fi
done
