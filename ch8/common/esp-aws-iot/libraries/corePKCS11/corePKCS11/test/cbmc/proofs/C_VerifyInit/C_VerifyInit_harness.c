/*
 * corePKCS11 v3.5.0
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * SPDX-License-Identifier: MIT
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

/**
 * @file C_VerifyInit_harness.c
 * @brief Implements the proof harness for C_VerifyInit function.
 */

#include <stddef.h>
#include "mbedtls/sha256.h"
#include "mbedtls/cmac.h"
#include "mbedtls/pk.h"
#include "core_pkcs11_config.h"
#include "core_pkcs11.h"

/* Internal struct for corePKCS11 mbed TLS implementation, but we don't really care what it contains
 * in this proof.
 *
 * It is just copied over from "core_pkcs11_mbedtls.c" so the structure is correct.
 */
typedef struct P11Session
{
    CK_ULONG ulState;
    CK_BBOOL xOpened;
    CK_MECHANISM_TYPE xOperationDigestMechanism;
    CK_BYTE * pxFindObjectLabel;
    CK_ULONG xFindObjectLabelLen;
    CK_MECHANISM_TYPE xOperationVerifyMechanism;
    mbedtls_threading_mutex_t xVerifyMutex;
    CK_OBJECT_HANDLE xVerifyKeyHandle;
    mbedtls_pk_context xVerifyKey;
    CK_MECHANISM_TYPE xOperationSignMechanism;
    mbedtls_threading_mutex_t xSignMutex;
    CK_OBJECT_HANDLE xSignKeyHandle;
    mbedtls_pk_context xSignKey;
    mbedtls_sha256_context xSHA256Context;
    CK_OBJECT_HANDLE xHMACKeyHandle;
    mbedtls_md_context_t xHMACSecretContext;
    CK_OBJECT_HANDLE xCMACKeyHandle;
    mbedtls_cipher_context_t xCMACSecretContext;
} P11Session_t;

CK_RV __CPROVER_file_local_core_pkcs11_mbedtls_c_prvCheckValidSessionAndModule( const P11Session_t * pxSession )
{
    CK_RV xResult;

    __CPROVER_assert( pxSession != NULL, "pxSession was NULL." );
    return xResult;
}

CK_BBOOL __CPROVER_file_local_core_pkcs11_mbedtls_c_prvOperationActive( const P11Session_t * pxSession )
{
    CK_BBOOL xBool;

    __CPROVER_assert( pxSession != NULL, "pxSession was NULL." );
    return xBool;
}

void __CPROVER_file_local_core_pkcs11_mbedtls_c_prvFindObjectInListByHandle( CK_OBJECT_HANDLE xAppHandle,
                                                                             CK_OBJECT_HANDLE_PTR pxPalHandle,
                                                                             CK_BYTE_PTR * ppcLabel,
                                                                             CK_ULONG_PTR pxLabelLength )
{
    CK_OBJECT_HANDLE handle;

    __CPROVER_assert( pxPalHandle != NULL, "ppcLabel was NULL." );
    __CPROVER_assert( ppcLabel != NULL, "ppcLabel was NULL." );
    __CPROVER_assert( pxLabelLength != NULL, "ppcLabel was NULL." );

    __CPROVER_assume( handle < MAX_OBJECT_NUM );
    *pxPalHandle = handle;
}

void harness()
{
    CK_MECHANISM * pxMechanism = malloc( sizeof( CK_MECHANISM ) );
    CK_OBJECT_HANDLE hKey;
    CK_SESSION_HANDLE xSession;

    __CPROVER_assume( ( xSession > CK_INVALID_HANDLE ) && ( xSession <= pkcs11configMAX_SESSIONS ) );
    ( void ) C_VerifyInit( xSession, pxMechanism, hKey );
}
