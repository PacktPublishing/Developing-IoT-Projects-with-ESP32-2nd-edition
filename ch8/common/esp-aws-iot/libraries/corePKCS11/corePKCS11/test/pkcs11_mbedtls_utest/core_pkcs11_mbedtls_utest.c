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

/* C runtime includes. */
#include <stdlib.h>
#include <stdbool.h>
#include <string.h>

/* Mock includes. */
#include "mock_ctr_drbg.h"
#include "mock_entropy.h"
#include "mock_sha256.h"
#include "mock_pk.h"
#include "mock_x509_crt.h"
#include "mock_ecp.h"
#include "mock_ecdsa.h"
#include "mock_mock_osal.h"
#include "mock_rsa.h"
#include "mock_bignum.h"
#include "mock_core_pki_utils.h"
#include "mock_pk_internal.h"
#include "mock_md.h"
#include "mock_cmac.h"
#include "mock_cipher.h"
#include "mock_malloc_stub.h"

/* PKCS #11 includes. */
#include "core_pkcs11_config.h"
#include "core_pkcs11.h"

/* This mock must be included after pkcs11.h */
#include "mock_core_pkcs11_pal.h"

/* mbedtls includes. */
#include "oid.h"

/* Test includes. */
#include "unity.h"


/* ============================  GLOBAL VARIABLES =========================== */
/* Length parameters for importing EC private keys. */
#define EC_PARAMS_LENGTH         10
#define EC_D_LENGTH              32

#define pkcs11EC_POINT_LENGTH    ( ( 32UL * 2UL ) + 1UL + 1UL + 1UL )

#define EC_PRIV_KEY_INITIALIZER                                                            \
    {                                                                                      \
        { CKA_CLASS, &xPrivateKeyClass, sizeof( CK_OBJECT_CLASS ) },                       \
        { CKA_KEY_TYPE, &xPrivateKeyType, sizeof( CK_KEY_TYPE ) },                         \
        { CKA_LABEL, pucPrivLabel, ( CK_ULONG ) strlen( ( const char * ) pucPrivLabel ) }, \
        { CKA_TOKEN, &xTrue, sizeof( CK_BBOOL ) },                                         \
        { CKA_SIGN, &xTrue, sizeof( CK_BBOOL ) },                                          \
        { CKA_EC_PARAMS, pxEcPrivParams, EC_PARAMS_LENGTH },                               \
        { CKA_VALUE, pxD, EC_D_LENGTH }                                                    \
    }

#define EC_PUB_KEY_INITIALIZER                                             \
    {                                                                      \
        { CKA_CLASS, &xPublicKeyClass, sizeof( xPublicKeyClass ) },        \
        { CKA_KEY_TYPE, &xPublicKeyType, sizeof( xPublicKeyType ) },       \
        { CKA_TOKEN, &xTrue, sizeof( xTrue ) },                            \
        { CKA_VERIFY, &xTrue, sizeof( xTrue ) },                           \
        { CKA_EC_PARAMS, pxEcPubParams, sizeof( pxEcPubParams ) },         \
        { CKA_EC_POINT, pxEcPoint, xLength + 2 },                          \
        { CKA_LABEL, pucPubLabel, strlen( ( const char * ) pucPubLabel ) } \
    }

/* Length parameters for importing RSA-2048 private keys. */
#define MODULUS_LENGTH        pkcs11RSA_2048_MODULUS_BITS / 8
#define E_LENGTH              3
#define D_LENGTH              pkcs11RSA_2048_MODULUS_BITS / 8
#define PRIME_1_LENGTH        128
#define PRIME_2_LENGTH        128
#define EXPONENT_1_LENGTH     128
#define EXPONENT_2_LENGTH     128
#define COEFFICIENT_LENGTH    128

#define RSA_PRIV_KEY_INITIALIZER                                                   \
    {                                                                              \
        { CKA_CLASS, &xPrivateKeyClass, sizeof( CK_OBJECT_CLASS ) },               \
        { CKA_KEY_TYPE, &xPrivateKeyType, sizeof( CK_KEY_TYPE ) },                 \
        { CKA_LABEL, pucLabel, ( CK_ULONG ) strlen( ( const char * ) pucLabel ) }, \
        { CKA_TOKEN, &xTrue, sizeof( CK_BBOOL ) },                                 \
        { CKA_SIGN, &xTrue, sizeof( CK_BBOOL ) },                                  \
        { CKA_MODULUS, xRsaParams.modulus + 1, MODULUS_LENGTH },                   \
        { CKA_PRIVATE_EXPONENT, xRsaParams.d + 1, D_LENGTH },                      \
        { CKA_PUBLIC_EXPONENT, xRsaParams.e + 1, E_LENGTH },                       \
        { CKA_PRIME_1, xRsaParams.prime1 + 1, PRIME_1_LENGTH },                    \
        { CKA_PRIME_2, xRsaParams.prime2 + 1, PRIME_2_LENGTH },                    \
        { CKA_EXPONENT_1, xRsaParams.exponent1 + 1, EXPONENT_1_LENGTH },           \
        { CKA_EXPONENT_2, xRsaParams.exponent2 + 1, EXPONENT_2_LENGTH },           \
        { CKA_COEFFICIENT, xRsaParams.coefficient + 1, COEFFICIENT_LENGTH }        \
    }

#define CERT_INITIALIZER                                                              \
    {                                                                                 \
        { CKA_CLASS, &xCertificateClass, sizeof( xCertificateClass ) },               \
        { CKA_SUBJECT, xSubject, strlen( ( const char * ) xSubject ) },               \
        { CKA_VALUE, ( CK_VOID_PTR ) xCert, ( CK_ULONG ) sizeof( xCert ) },           \
        { CKA_LABEL, ( CK_VOID_PTR ) pucLabel, strlen( ( const char * ) pucLabel ) }, \
        { CKA_CERTIFICATE_TYPE, &xCertificateType, sizeof( CK_CERTIFICATE_TYPE ) },   \
        { CKA_TOKEN, &xTokenStorage, sizeof( xTokenStorage ) }                        \
    }


/*
 * @brief Macro taken from "core_pkcs11_mbedtls.c"
 */
#define pkcs11_PRIVATE_EC_PRIME_256_DER_SIZE    160

/* Malloc calls */
static uint16_t usMallocFreeCalls = 0;

static mbedtls_pk_type_t xPkType = MBEDTLS_PK_NONE;

/* Internal struct to facilitate passing RSA params to mbedTLS. */

/* Adding one to all of the lengths because ASN1 may pad a leading 0 byte
 * to numbers that could be interpreted as negative */
typedef struct RsaParams_t
{
    CK_BYTE modulus[ MODULUS_LENGTH + 1 ];
    CK_BYTE e[ E_LENGTH + 1 ];
    CK_BYTE d[ D_LENGTH + 1 ];
    CK_BYTE prime1[ PRIME_1_LENGTH + 1 ];
    CK_BYTE prime2[ PRIME_2_LENGTH + 1 ];
    CK_BYTE exponent1[ EXPONENT_1_LENGTH + 1 ];
    CK_BYTE exponent2[ EXPONENT_2_LENGTH + 1 ];
    CK_BYTE coefficient[ COEFFICIENT_LENGTH + 1 ];
} RsaParams_t;

/* ==========================  MBED TLS EXTERNS =========================== */
/* Extern struct used by mbed TLS internally for managing RSA structs. */
const mbedtls_pk_info_t mbedtls_rsa_info =
{
    MBEDTLS_PK_RSA,
    "RSA",
    NULL,
    NULL,
    NULL,
    NULL,
    NULL,
    NULL,
    NULL,
    NULL,
    NULL,
    NULL,
};

const mbedtls_pk_info_t mbedtls_eckey_info =
{
    MBEDTLS_PK_ECKEY,
    "EC",
    NULL,
    NULL,
    #if defined( MBEDTLS_ECDSA_C )
        NULL,
        NULL,
    #else
        NULL,
        NULL,
    #endif
    NULL,
    NULL,
    NULL,
    NULL,
    NULL,
    NULL,
};

/* ==========================  CALLBACK FUNCTIONS =========================== */

static void * pvPkcs11CallocCb( size_t nitems,
                                size_t size,
                                int numCalls )
{
    usMallocFreeCalls++;
    return ( void * ) calloc( nitems, size );
}

static void vPkcs11FreeCb( void * pvPtr,
                           int numCalls )
{
    if( pvPtr != NULL )
    {
        usMallocFreeCalls--;
        free( pvPtr );
    }
}

void (* mbedtls_mutex_init)( mbedtls_threading_mutex_t * ) = &mock_osal_mutex_init;
void (* mbedtls_mutex_free)( mbedtls_threading_mutex_t * ) = &mock_osal_mutex_free;
int (* mbedtls_mutex_lock)( mbedtls_threading_mutex_t * ) = &mock_osal_mutex_lock;
int (* mbedtls_mutex_unlock)( mbedtls_threading_mutex_t * ) = &mock_osal_mutex_unlock;

const mbedtls_pk_info_t * pk_info_from_type_stub( mbedtls_pk_type_t pk_type,
                                                  int numCalls )
{
    const mbedtls_pk_info_t * pxPkInfo = NULL;

    ( void ) numCalls;

    switch( pk_type )
    {
        case MBEDTLS_PK_RSA:
            pxPkInfo = &mbedtls_rsa_info;
            break;

        case MBEDTLS_PK_ECKEY:
            pxPkInfo = &mbedtls_eckey_info;
            break;

        default:
            pxPkInfo = NULL;
            break;
    }

    return pxPkInfo;
}

static mbedtls_pk_type_t pk_get_type_stub( const mbedtls_pk_context * ctx,
                                           int cmock_num_calls )
{
    ( void ) ctx;
    ( void ) cmock_num_calls;

    return xPkType;
}

/* ============================   UNITY FIXTURES ============================ */
void setUp( void )
{
    mbedtls_pk_info_from_type_Stub( pk_info_from_type_stub );
}

/* called before each testcase */
void tearDown( void )
{
    TEST_ASSERT_EQUAL_INT_MESSAGE( 0, usMallocFreeCalls,
                                   "free is not called the same number of times as malloc, \
        you might have a memory leak!!" );
    usMallocFreeCalls = 0;
}

/* called at the beginning of the whole suite */
void suiteSetUp()
{
    usMallocFreeCalls = 0;
}

/* called at the end of the whole suite */
int suiteTearDown( int numFailures )
{
    return numFailures;
}

/* ==========================  Helper functions  ============================ */

/*!
 * @brief Helper function to stub mbedtls_pk_free.
 *
 */
void vMbedPkFree( mbedtls_pk_context * pxCtx,
                  int lCallCount )
{
    ( void ) lCallCount;
    vPkcs11FreeCb( pxCtx->pk_ctx, 1 );
}

/*!
 * @brief Helper function to initialize PKCS #11.
 *
 */
static CK_RV prvInitializePkcs11()
{
    CK_RV xResult = CKR_OK;

    PKCS11_PAL_Initialize_IgnoreAndReturn( CKR_OK );
    mock_osal_mutex_init_CMockIgnore();
    mbedtls_entropy_init_Ignore();
    mbedtls_ctr_drbg_init_Ignore();
    mbedtls_ctr_drbg_seed_IgnoreAndReturn( 0 );
    xResult = C_Initialize( NULL );

    return xResult;
}

/*!
 * @brief Helper function to initialize PKCS #11.
 *
 */
static CK_RV prvUninitializePkcs11()
{
    CK_RV xResult = CKR_OK;

    mbedtls_entropy_free_CMockIgnore();
    mbedtls_ctr_drbg_free_CMockIgnore();
    mock_osal_mutex_free_CMockIgnore();
    xResult = C_Finalize( NULL );

    return xResult;
}

/*!
 * @brief Helper function to create a PKCS #11 session.
 *
 */
static CK_RV prvOpenSession( CK_SESSION_HANDLE_PTR pxSession )
{
    CK_RV xResult = CKR_OK;
    CK_FLAGS xFlags = CKF_SERIAL_SESSION | CKF_RW_SESSION;

    mbedtls_calloc_Stub( pvPkcs11CallocCb );
    mock_osal_mutex_lock_IgnoreAndReturn( 0 );
    mock_osal_mutex_unlock_IgnoreAndReturn( 0 );
    mock_osal_mutex_init_CMockIgnore();
    xResult = C_OpenSession( 0, xFlags, NULL, 0, pxSession );

    return xResult;
}

/*!
 * @brief Helper function to close a PKCS #11 session.
 *
 */
static CK_RV prvCloseSession( CK_SESSION_HANDLE_PTR pxSession )
{
    CK_RV xResult = CKR_OK;

    mock_osal_mutex_free_CMockIgnore();
    mbedtls_pk_free_CMockIgnore();
    vPkcs11Free_Stub( vPkcs11FreeCb );
    mbedtls_free_Stub( vPkcs11FreeCb );
    mbedtls_sha256_free_CMockIgnore();
    xResult = C_CloseSession( *pxSession );

    return xResult;
}

static void prvCommonInitStubs( CK_SESSION_HANDLE_PTR pxSession )
{
    CK_RV xResult = CKR_OK;

    xResult = prvInitializePkcs11();
    TEST_ASSERT_EQUAL( CKR_OK, xResult );
    xResult = prvOpenSession( pxSession );
    TEST_ASSERT_EQUAL( CKR_OK, xResult );

    mbedtls_pk_get_type_Stub( pk_get_type_stub );
}

static void prvCommonDeinitStubs( CK_SESSION_HANDLE_PTR pxSession )
{
    CK_RV xResult = CKR_OK;

    xResult = prvCloseSession( pxSession );
    /* Can't check xResult here. First TEST_ASSERT will exit TEST_PROTECT block. */

    if( xResult == CKR_OK )
    {
        xResult = prvUninitializePkcs11();
    }

    TEST_ASSERT_EQUAL( CKR_OK, xResult );
}


/*!
 * @brief Helper function to create a x509 certificate.
 *
 */
static CK_RV prvCreateCert( CK_SESSION_HANDLE_PTR pxSession,
                            CK_OBJECT_HANDLE_PTR pxObject )
{
    CK_RV xResult = CKR_OK;

    CK_OBJECT_CLASS xCertificateClass = CKO_CERTIFICATE;
    CK_CERTIFICATE_TYPE xCertificateType = CKC_X_509;
    CK_BBOOL xTokenStorage = CK_TRUE;
    CK_BYTE xSubject[] = "TestSubject";
    CK_BYTE xCert[] = "Empty Cert";
    char * pucLabel = pkcs11configLABEL_DEVICE_CERTIFICATE_FOR_TLS;
    PKCS11_CertificateTemplate_t xTemplate = CERT_INITIALIZER;

    /* Create Certificate. */
    PKCS11_PAL_SaveObject_IgnoreAndReturn( 3 );
    mock_osal_mutex_lock_IgnoreAndReturn( 0 );
    mock_osal_mutex_unlock_IgnoreAndReturn( 0 );
    xResult = C_CreateObject( *pxSession,
                              ( CK_ATTRIBUTE_PTR ) &xTemplate,
                              sizeof( xTemplate ) / sizeof( CK_ATTRIBUTE ),
                              pxObject );
    return xResult;
}

/*!
 * @brief Helper function to create an EC Private Key.
 *
 */
static CK_RV prvCreateEcPriv( CK_SESSION_HANDLE_PTR pxSession,
                              CK_OBJECT_HANDLE_PTR pxObject )
{
    CK_RV xResult = CKR_OK;
    CK_KEY_TYPE xPrivateKeyType = CKK_EC;
    CK_OBJECT_CLASS xPrivateKeyClass = CKO_PRIVATE_KEY;
    CK_BBOOL xTrue = CK_TRUE;
    char * pucPrivLabel = pkcs11configLABEL_DEVICE_PRIVATE_KEY_FOR_TLS;

    /* DER-encoding of an ANSI X9.62 Parameters value */
    CK_BYTE * pxEcPrivParams = ( CK_BYTE * ) ( "\x06\x08" MBEDTLS_OID_EC_GRP_SECP256R1 );

    /* Private value D. */
    CK_BYTE pxD[ EC_D_LENGTH ] = { 0 };

    CK_ATTRIBUTE xPrivateKeyTemplate[] = EC_PRIV_KEY_INITIALIZER;

    mbedtls_pk_init_CMockIgnore();
    mbedtls_calloc_Stub( pvPkcs11CallocCb );
    PKCS11_PAL_FindObject_IgnoreAndReturn( 2 );
    PKCS11_PAL_GetObjectValue_IgnoreAndReturn( CKR_OK );
    mbedtls_pk_parse_key_IgnoreAndReturn( 0 );
    PKCS11_PAL_GetObjectValueCleanup_CMockIgnore();
    mbedtls_ecp_keypair_init_CMockIgnore();
    mbedtls_ecp_group_init_CMockIgnore();
    mbedtls_ecp_group_load_IgnoreAndReturn( 0 );
    mbedtls_mpi_read_binary_IgnoreAndReturn( 0 );
    mbedtls_pk_write_key_der_IgnoreAndReturn( 1 );
    mbedtls_pk_free_CMockIgnore();
    PKCS11_PAL_SaveObject_IgnoreAndReturn( 2 );
    mock_osal_mutex_lock_IgnoreAndReturn( 0 );
    mock_osal_mutex_unlock_IgnoreAndReturn( 0 );
    vPkcs11Free_Stub( vPkcs11FreeCb );
    mbedtls_free_Stub( vPkcs11FreeCb );
    xResult = C_CreateObject( *pxSession,
                              ( CK_ATTRIBUTE_PTR ) &xPrivateKeyTemplate,
                              sizeof( xPrivateKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                              pxObject );

    return xResult;
}

/*!
 * @brief Helper function to create an RSA Private Key.
 *
 */
static CK_RV prvCreateRsaPriv( CK_SESSION_HANDLE_PTR pxSession,
                               CK_OBJECT_HANDLE_PTR pxObject )
{
    CK_RV xResult = CKR_OK;
    CK_KEY_TYPE xPrivateKeyType = CKK_RSA;
    CK_OBJECT_CLASS xPrivateKeyClass = CKO_PRIVATE_KEY;
    CK_BBOOL xTrue = CK_TRUE;
    char * pucLabel = pkcs11configLABEL_DEVICE_PRIVATE_KEY_FOR_TLS;
    RsaParams_t xRsaParams = { 0 };
    CK_ATTRIBUTE xPrivateKeyTemplate[] = RSA_PRIV_KEY_INITIALIZER;

    mbedtls_pk_init_CMockIgnore();
    mbedtls_calloc_Stub( pvPkcs11CallocCb );
    mbedtls_rsa_init_CMockIgnore();
    mbedtls_rsa_import_raw_IgnoreAndReturn( 0 );
    mbedtls_mpi_read_binary_IgnoreAndReturn( 0 );
    mbedtls_pk_write_key_der_IgnoreAndReturn( 1 );
    mbedtls_pk_free_Stub( vMbedPkFree );
    PKCS11_PAL_SaveObject_IgnoreAndReturn( 1 );
    mock_osal_mutex_lock_IgnoreAndReturn( 0 );
    mock_osal_mutex_unlock_IgnoreAndReturn( 0 );
    vPkcs11Free_Stub( vPkcs11FreeCb );
    mbedtls_free_Stub( vPkcs11FreeCb );
    xResult = C_CreateObject( *pxSession,
                              ( CK_ATTRIBUTE_PTR ) &xPrivateKeyTemplate,
                              sizeof( xPrivateKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                              pxObject );

    return xResult;
}

/*!
 * @brief Helper function to create a EC Public Key.
 *
 */
static CK_RV prvCreateEcPub( CK_SESSION_HANDLE_PTR pxSession,
                             CK_OBJECT_HANDLE_PTR pxObject )
{
    CK_RV xResult = CKR_OK;

    CK_KEY_TYPE xPublicKeyType = CKK_EC;
    CK_OBJECT_CLASS xPublicKeyClass = CKO_PUBLIC_KEY;
    CK_BBOOL xTrue = CK_TRUE;
    char * pucPubLabel = pkcs11configLABEL_DEVICE_PUBLIC_KEY_FOR_TLS;
    size_t xLength = 256;
    /* DER-encoding of an ANSI X9.62 Parameters value */
    CK_BYTE pxEcPubParams[] = pkcs11DER_ENCODED_OID_P256;
    CK_BYTE pxEcPoint[ 256 ] = { 0 };

    CK_ATTRIBUTE xTemplate[] = EC_PUB_KEY_INITIALIZER;

    /* Create  EC based public key. */
    mbedtls_pk_init_CMockIgnore();
    mbedtls_calloc_Stub( pvPkcs11CallocCb );
    PKCS11_PAL_FindObject_IgnoreAndReturn( 1 );
    PKCS11_PAL_GetObjectValue_IgnoreAndReturn( CKR_OK );
    mbedtls_pk_parse_public_key_IgnoreAndReturn( 0 );
    PKCS11_PAL_GetObjectValueCleanup_CMockIgnore();
    mbedtls_ecp_keypair_init_CMockIgnore();
    mbedtls_ecp_group_init_CMockIgnore();
    mbedtls_ecp_group_load_IgnoreAndReturn( 0 );
    mbedtls_ecp_point_read_binary_IgnoreAndReturn( 0 );
    mbedtls_mpi_read_binary_IgnoreAndReturn( 0 );
    mbedtls_pk_write_pubkey_der_IgnoreAndReturn( 1 );
    mbedtls_pk_free_CMockIgnore();
    PKCS11_PAL_SaveObject_IgnoreAndReturn( 1 );
    mock_osal_mutex_lock_IgnoreAndReturn( 0 );
    mock_osal_mutex_unlock_IgnoreAndReturn( 0 );
    vPkcs11Free_Stub( vPkcs11FreeCb );
    mbedtls_free_Stub( vPkcs11FreeCb );
    xResult = C_CreateObject( *pxSession,
                              ( CK_ATTRIBUTE_PTR ) &xTemplate,
                              sizeof( xTemplate ) / sizeof( CK_ATTRIBUTE ),
                              pxObject );


    return xResult;
}

/*!
 * @brief Helper function to create an RSA Public Key.
 *
 */
static CK_RV prvCreateRSAPub( CK_SESSION_HANDLE_PTR pxSession,
                              CK_OBJECT_HANDLE_PTR pxObject )
{
    CK_RV xResult = CKR_OK;
    CK_KEY_TYPE xPublicKeyType = CKK_RSA;
    CK_OBJECT_CLASS xClass = CKO_PUBLIC_KEY;
    CK_BBOOL xTrue = CK_TRUE;
    CK_BYTE xPublicExponent[] = { 0x01, 0x00, 0x01 };
    CK_BYTE xModulus[ MODULUS_LENGTH + 1 ] = { 0 };
    CK_BYTE pucPublicKeyLabel[] = pkcs11configLABEL_DEVICE_PUBLIC_KEY_FOR_TLS;

    CK_ATTRIBUTE xPublicKeyTemplate[] =
    {
        { CKA_CLASS,           &xClass,           sizeof( CK_OBJECT_CLASS )                    },
        { CKA_KEY_TYPE,        &xPublicKeyType,   sizeof( CK_KEY_TYPE )                        },
        { CKA_TOKEN,           &xTrue,            sizeof( xTrue )                              },
        { CKA_MODULUS,         &xModulus + 1,     MODULUS_LENGTH                               },
        { CKA_VERIFY,          &xTrue,            sizeof( xTrue )                              },
        { CKA_PUBLIC_EXPONENT, xPublicExponent,   sizeof( xPublicExponent )                    },
        { CKA_LABEL,           pucPublicKeyLabel, strlen( ( const char * ) pucPublicKeyLabel ) }
    };

    mbedtls_pk_init_ExpectAnyArgs();
    mbedtls_calloc_Stub( pvPkcs11CallocCb );
    mbedtls_rsa_init_CMockIgnore();
    mbedtls_rsa_import_raw_IgnoreAndReturn( 0 );
    mbedtls_pk_write_pubkey_der_IgnoreAndReturn( 1 );
    mbedtls_pk_free_Stub( vMbedPkFree );
    PKCS11_PAL_SaveObject_IgnoreAndReturn( 1 );
    mock_osal_mutex_lock_IgnoreAndReturn( 0 );
    mock_osal_mutex_unlock_IgnoreAndReturn( 0 );
    vPkcs11Free_Stub( vPkcs11FreeCb );
    mbedtls_free_Stub( vPkcs11FreeCb );
    xResult = C_CreateObject( *pxSession,
                              ( CK_ATTRIBUTE_PTR ) &xPublicKeyTemplate,
                              sizeof( xPublicKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                              pxObject );

    return xResult;
}

/*!
 * @brief Helper function to create a SHA256HMAC Key.
 *
 */
static CK_RV prvCreateSHA256HMAC( CK_SESSION_HANDLE_PTR pxSession,
                                  CK_OBJECT_HANDLE_PTR pxObject )
{
    CK_RV xResult = CKR_OK;
    CK_KEY_TYPE xKeyType = CKK_SHA256_HMAC;
    CK_OBJECT_CLASS xKeyClass = CKO_SECRET_KEY;
    CK_BBOOL xTrue = CK_TRUE;
    CK_BYTE pcLabel[] = pkcs11configLABEL_HMAC_KEY;

    CK_BYTE pxKeyValue[] = "abcdabcdabcdabcdabcdabcdabcdabcd";

    CK_ATTRIBUTE xSHA256HMACTemplate[] =
    {
        { CKA_CLASS,    &xKeyClass, sizeof( CK_OBJECT_CLASS ) },
        { CKA_KEY_TYPE, &xKeyType,  sizeof( CK_KEY_TYPE )     },
        { CKA_LABEL,    pcLabel,    sizeof( pcLabel ) - 1     },
        { CKA_TOKEN,    &xTrue,     sizeof( CK_BBOOL )        },
        { CKA_SIGN,     &xTrue,     sizeof( CK_BBOOL )        },
        { CKA_VERIFY,   &xTrue,     sizeof( CK_BBOOL )        },
        { CKA_VALUE,    pxKeyValue, sizeof( pxKeyValue ) - 1  }
    };

    PKCS11_PAL_SaveObject_IgnoreAndReturn( 1 );
    mock_osal_mutex_lock_IgnoreAndReturn( 0 );
    mock_osal_mutex_unlock_IgnoreAndReturn( 0 );
    xResult = C_CreateObject( *pxSession,
                              ( CK_ATTRIBUTE_PTR ) &xSHA256HMACTemplate,
                              sizeof( xSHA256HMACTemplate ) / sizeof( CK_ATTRIBUTE ),
                              pxObject );

    return xResult;
}

/*!
 * @brief Helper function to create a SHA256HMAC Key.
 *
 */
static CK_RV prvCreateAESCMAC( CK_SESSION_HANDLE_PTR pxSession,
                               CK_OBJECT_HANDLE_PTR pxObject )
{
    CK_RV xResult = CKR_OK;
    CK_KEY_TYPE xKeyType = CKK_AES;
    CK_OBJECT_CLASS xKeyClass = CKO_SECRET_KEY;
    CK_BBOOL xTrue = CK_TRUE;
    CK_BYTE pcLabel[] = pkcs11configLABEL_CMAC_KEY;

    CK_BYTE pxKeyValue[] =
    {
        0x11, 0x22, 0x33, 0x44,
        0x11, 0x22, 0x33, 0x44,
        0x11, 0x22, 0x33, 0x44,
        0x11, 0x22, 0x33, 0x44
    };

    CK_ATTRIBUTE xAESCMACTemplate[] =
    {
        { CKA_CLASS,    &xKeyClass, sizeof( CK_OBJECT_CLASS ) },
        { CKA_KEY_TYPE, &xKeyType,  sizeof( CK_KEY_TYPE )     },
        { CKA_LABEL,    pcLabel,    sizeof( pcLabel ) - 1     },
        { CKA_TOKEN,    &xTrue,     sizeof( CK_BBOOL )        },
        { CKA_SIGN,     &xTrue,     sizeof( CK_BBOOL )        },
        { CKA_VERIFY,   &xTrue,     sizeof( CK_BBOOL )        },
        { CKA_VALUE,    pxKeyValue, sizeof( pxKeyValue )      }
    };

    PKCS11_PAL_SaveObject_IgnoreAndReturn( 1 );
    mock_osal_mutex_lock_IgnoreAndReturn( 0 );
    mock_osal_mutex_unlock_IgnoreAndReturn( 0 );
    xResult = C_CreateObject( *pxSession,
                              ( CK_ATTRIBUTE_PTR ) &xAESCMACTemplate,
                              sizeof( xAESCMACTemplate ) / sizeof( CK_ATTRIBUTE ),
                              pxObject );

    return xResult;
}

/* ======================  TESTING C_Initialize  ============================ */

/*!
 * @brief C_Initialize happy path.
 *
 */
void test_pkcs11_C_Initialize( void )
{
    CK_RV xResult = CKR_OK;

    PKCS11_PAL_Initialize_IgnoreAndReturn( CKR_OK );
    mock_osal_mutex_init_CMockIgnore();
    mbedtls_entropy_init_Ignore();
    mbedtls_ctr_drbg_init_Ignore();
    mbedtls_ctr_drbg_seed_IgnoreAndReturn( 0 );
    xResult = C_Initialize( NULL );
    TEST_ASSERT_EQUAL( CKR_OK, xResult );

    xResult = prvUninitializePkcs11();
    TEST_ASSERT_EQUAL( CKR_OK, xResult );
}

/*!
 * @brief C_Initialize failed to seed DRBG.
 *
 */
void test_pkcs11_C_InitializeSeedFail( void )
{
    CK_RV xResult = CKR_OK;

    PKCS11_PAL_Initialize_IgnoreAndReturn( CKR_OK );
    mock_osal_mutex_init_CMockIgnore();
    mbedtls_entropy_init_Ignore();
    mbedtls_ctr_drbg_init_Ignore();
    mbedtls_ctr_drbg_seed_IgnoreAndReturn( 1 );
    xResult = C_Initialize( NULL );

    TEST_ASSERT_EQUAL( CKR_FUNCTION_FAILED, xResult );
}

/*!
 * @brief C_Initialize already initialized.
 *
 */
void test_pkcs11_C_InitializeInitTwice( void )
{
    CK_RV xResult = CKR_OK;

    xResult = prvInitializePkcs11();
    TEST_ASSERT_EQUAL( CKR_OK, xResult );

    xResult = C_Initialize( NULL );
    TEST_ASSERT_EQUAL( CKR_CRYPTOKI_ALREADY_INITIALIZED, xResult );

    xResult = prvUninitializePkcs11();
    TEST_ASSERT_EQUAL( CKR_OK, xResult );
}

/* ======================  TESTING C_Finalize  ============================ */

/*!
 * @brief C_Finalize initialize was not already called.
 *
 */
void test_pkcs11_C_FinalizeUninitialized( void )
{
    CK_RV xResult = CKR_OK;

    mbedtls_entropy_free_CMockIgnore();
    mbedtls_ctr_drbg_free_CMockIgnore();
    mock_osal_mutex_free_CMockIgnore();
    xResult = C_Finalize( NULL );
    TEST_ASSERT_EQUAL( CKR_CRYPTOKI_NOT_INITIALIZED, xResult );
}

/*!
 * @brief C_Finalize was called with a non-null pointer.
 *
 */
void test_pkcs11_C_FinalizeBadArgs( void )
{
    CK_RV xResult = CKR_OK;

    mbedtls_entropy_free_CMockIgnore();
    mbedtls_ctr_drbg_free_CMockIgnore();
    mock_osal_mutex_free_CMockIgnore();
    xResult = C_Finalize( ( CK_VOID_PTR ) &xResult );

    TEST_ASSERT_EQUAL( CKR_ARGUMENTS_BAD, xResult );
}

/* ======================  TESTING C_GetFunctionList  ============================ */

/*!
 * @brief C_GetFunctionList happy path.
 *
 */
void test_pkcs11_C_GetFunctionList( void )
{
    CK_RV xResult = CKR_OK;
    CK_FUNCTION_LIST_PTR pxFunctionList = NULL;

    xResult = C_GetFunctionList( &pxFunctionList );

    TEST_ASSERT_EQUAL( CKR_OK, xResult );
}

/*!
 * @brief C_GetFunctionList bad args.
 *
 */
void test_pkcs11_C_GetFunctionListBadArgs( void )
{
    CK_RV xResult = CKR_OK;

    xResult = C_GetFunctionList( NULL );

    TEST_ASSERT_EQUAL( CKR_ARGUMENTS_BAD, xResult );
}

/* ======================  TESTING C_GetSlotList  ============================ */

/*!
 * @brief C_GetSlotList happy path.
 *
 */
void test_pkcs11_C_GetSlotList( void )
{
    CK_RV xResult = CKR_OK;
    CK_SLOT_ID xSlotId = 0;
    CK_ULONG xSlotCount = 1;
    CK_BBOOL xTokenPresent = CK_TRUE;

    xResult = prvInitializePkcs11();
    TEST_ASSERT_EQUAL( CKR_OK, xResult );

    if( TEST_PROTECT() )
    {
        xResult = C_GetSlotList( xTokenPresent, &xSlotId, &xSlotCount );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );
        TEST_ASSERT_EQUAL( 1, xSlotCount );

        xResult = C_GetSlotList( xTokenPresent, &xSlotId, &xSlotCount );

        TEST_ASSERT_EQUAL( CKR_OK, xResult );
        TEST_ASSERT_EQUAL( 1, xSlotCount );
        TEST_ASSERT_EQUAL( 1, xSlotId );
    }

    xResult = prvUninitializePkcs11();
    TEST_ASSERT_EQUAL( CKR_OK, xResult );
}

/*!
 * @brief C_GetSlotList NULL SlotList.
 *
 */
void test_pkcs11_C_GetSlotListNullSlot( void )
{
    CK_RV xResult = CKR_OK;
    CK_ULONG xSlotCount = 0;
    CK_BBOOL xTokenPresent = CK_TRUE;

    xResult = prvInitializePkcs11();
    TEST_ASSERT_EQUAL( CKR_OK, xResult );

    if( TEST_PROTECT() )
    {
        xResult = C_GetSlotList( xTokenPresent, NULL, &xSlotCount );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        TEST_ASSERT_EQUAL( CKR_OK, xResult );
        TEST_ASSERT_EQUAL( 1, xSlotCount );
    }

    xResult = prvUninitializePkcs11();
    TEST_ASSERT_EQUAL( CKR_OK, xResult );
}

/*!
 * @brief C_GetSlotList NULL SlotCount.
 *
 */
void test_pkcs11_C_GetSlotListNullCount( void )
{
    CK_RV xResult = CKR_OK;
    CK_BBOOL xTokenPresent = CK_TRUE;

    xResult = prvInitializePkcs11();
    TEST_ASSERT_EQUAL( CKR_OK, xResult );

    if( TEST_PROTECT() )
    {
        xResult = C_GetSlotList( xTokenPresent, NULL, NULL );
        TEST_ASSERT_EQUAL( CKR_ARGUMENTS_BAD, xResult );
    }

    xResult = prvUninitializePkcs11();
    TEST_ASSERT_EQUAL( CKR_OK, xResult );
}

/*!
 * @brief C_GetSlotList 0 object count, valid slotlist.
 *
 */
void test_pkcs11_C_GetSlotListBadObjCount( void )
{
    CK_RV xResult = CKR_OK;
    CK_SLOT_ID xSlotId = 1;
    CK_ULONG xSlotCount = 0;
    CK_BBOOL xTokenPresent = CK_TRUE;

    xResult = prvInitializePkcs11();
    TEST_ASSERT_EQUAL( CKR_OK, xResult );

    if( TEST_PROTECT() )
    {
        xResult = C_GetSlotList( xTokenPresent, &xSlotId, &xSlotCount );

        TEST_ASSERT_EQUAL( CKR_BUFFER_TOO_SMALL, xResult );
        TEST_ASSERT_EQUAL( 0, xSlotCount );
        TEST_ASSERT_EQUAL( 1, xSlotId );
    }

    xResult = prvUninitializePkcs11();
    TEST_ASSERT_EQUAL( CKR_OK, xResult );
}

/*!
 * @brief C_GetSlotList PKCS #11 Not initialized.
 *
 */
void test_pkcs11_C_GetSlotListUninit( void )
{
    CK_RV xResult = CKR_OK;
    CK_SLOT_ID xSlotId = 1;
    CK_ULONG xSlotCount = 1;
    CK_BBOOL xTokenPresent = CK_TRUE;

    xResult = C_GetSlotList( xTokenPresent, &xSlotId, &xSlotCount );

    TEST_ASSERT_EQUAL( CKR_CRYPTOKI_NOT_INITIALIZED, xResult );
    TEST_ASSERT_EQUAL( 1, xSlotCount );
    TEST_ASSERT_EQUAL( 1, xSlotId );
}

/* ======================  TESTING C_GetTokenInfo  ============================ */

/*!
 * @brief C_GetTokenInfo Happy path.
 *
 * @note this test will need to be updated if this port needs to start returning
 * token information.
 *
 */
void test_pkcs11_C_GetTokenInfo( void )
{
    CK_RV xResult = CKR_OK;

    xResult = C_GetTokenInfo( 0, NULL );
    TEST_ASSERT_EQUAL( CKR_OK, xResult );
}
/* ======================  TESTING C_GetMechanismInfo  ============================ */

/*!
 * @brief C_GetMechanismInfo happy path.
 *
 */
void test_pkcs11_C_GetMechanismInfo( void )
{
    CK_RV xResult = CKR_OK;
    CK_MECHANISM_TYPE xType = CKM_RSA_PKCS;
    CK_MECHANISM_INFO xInfo = { 0 };

    xResult = C_GetMechanismInfo( 0, xType, &xInfo );

    TEST_ASSERT_EQUAL( 2048, xInfo.ulMinKeySize );
    TEST_ASSERT_EQUAL( 2048, xInfo.ulMaxKeySize );
    TEST_ASSERT_EQUAL( CKF_SIGN, xInfo.flags );
    TEST_ASSERT_EQUAL( CKR_OK, xResult );

    xType = CKM_RSA_X_509;
    memset( &xInfo, 0, sizeof( CK_MECHANISM_INFO ) );
    xResult = C_GetMechanismInfo( 0, xType, &xInfo );

    TEST_ASSERT_EQUAL( 2048, xInfo.ulMinKeySize );
    TEST_ASSERT_EQUAL( 2048, xInfo.ulMaxKeySize );
    TEST_ASSERT_EQUAL( CKF_VERIFY, xInfo.flags );
    TEST_ASSERT_EQUAL( CKR_OK, xResult );

    #ifndef pkcs11configSUPPRESS_ECDSA_MECHANISM
        xType = CKM_ECDSA;
        memset( &xInfo, 0, sizeof( CK_MECHANISM_INFO ) );
        xResult = C_GetMechanismInfo( 0, xType, &xInfo );

        TEST_ASSERT_EQUAL( 256, xInfo.ulMinKeySize );
        TEST_ASSERT_EQUAL( 256, xInfo.ulMaxKeySize );
        TEST_ASSERT_EQUAL( CKF_SIGN | CKF_VERIFY, xInfo.flags );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        xType = CKM_EC_KEY_PAIR_GEN;
        memset( &xInfo, 0, sizeof( CK_MECHANISM_INFO ) );
        xResult = C_GetMechanismInfo( 0, xType, &xInfo );

        TEST_ASSERT_EQUAL( 256, xInfo.ulMinKeySize );
        TEST_ASSERT_EQUAL( 256, xInfo.ulMaxKeySize );
        TEST_ASSERT_EQUAL( CKF_GENERATE_KEY_PAIR, xInfo.flags );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );
    #endif /* #ifdef pkcs11configSUPPRESS_ECDSA_MECHANISM */

    xType = CKM_SHA256;
    memset( &xInfo, 0, sizeof( CK_MECHANISM_INFO ) );
    xResult = C_GetMechanismInfo( 0, xType, &xInfo );

    TEST_ASSERT_EQUAL( 0, xInfo.ulMinKeySize );
    TEST_ASSERT_EQUAL( 0, xInfo.ulMaxKeySize );
    TEST_ASSERT_EQUAL( CKF_DIGEST, xInfo.flags );
    TEST_ASSERT_EQUAL( CKR_OK, xResult );
}

/*!
 * @brief C_GetMechanismInfo NULL info pointer.
 *
 */
void test_pkcs11_C_GetMechanismInfoNullInfoPtr( void )
{
    CK_RV xResult = CKR_OK;
    CK_MECHANISM_TYPE xType = CKM_RSA_PKCS;

    xResult = C_GetMechanismInfo( 0, xType, NULL );
    TEST_ASSERT_EQUAL( CKR_ARGUMENTS_BAD, xResult );
}

/*!
 * @brief C_GetMechanismInfo Bad Mechanism.
 *
 */
void test_pkcs11_C_GetMechanismInfoBadMech( void )
{
    CK_RV xResult = CKR_OK;
    CK_MECHANISM_TYPE xType = -1;
    CK_MECHANISM_INFO xInfo = { 0 };

    xResult = C_GetMechanismInfo( 0, xType, &xInfo );
    TEST_ASSERT_EQUAL( CKR_MECHANISM_INVALID, xResult );
}

/* ======================  TESTING C_InitToken  ============================ */

/*!
 * @brief C_InitToken Happy path.
 *
 * @note currently the port behaves like a fixed token, and doesn't do anything
 * when this function is called.
 *
 */
void test_pkcs11_C_InitToken( void )
{
    CK_RV xResult = CKR_OK;

    xResult = C_InitToken( 0, NULL, 0, NULL );
    TEST_ASSERT_EQUAL( CKR_OK, xResult );
}
/* ======================  TESTING C_OpenSession  ============================ */

/*!
 * @brief C_OpenSession happy path.
 *
 */
void test_pkcs11_C_OpenSession( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = 0;
    CK_FLAGS xFlags = CKF_SERIAL_SESSION | CKF_RW_SESSION;

    xResult = prvInitializePkcs11();
    TEST_ASSERT_EQUAL( CKR_OK, xResult );

    if( TEST_PROTECT() )
    {
        mbedtls_calloc_Stub( pvPkcs11CallocCb );
        mock_osal_mutex_lock_IgnoreAndReturn( 0 );
        mock_osal_mutex_unlock_IgnoreAndReturn( 0 );
        mock_osal_mutex_init_CMockIgnore();
        xResult = C_OpenSession( 0, xFlags, NULL, 0, &xSession );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );
    }

    xResult = prvUninitializePkcs11();
    TEST_ASSERT_EQUAL( CKR_OK, xResult );
}

/*!
 * @brief C_OpenSession PKCS #11 Uninitialized.
 *
 */
void test_pkcs11_C_OpenSessionUninit( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = 0;
    CK_FLAGS xFlags = CKF_SERIAL_SESSION | CKF_RW_SESSION;

    xResult = C_OpenSession( 0, xFlags, NULL, 0, &xSession );
    TEST_ASSERT_EQUAL( CKR_CRYPTOKI_NOT_INITIALIZED, xResult );
}

/*!
 * @brief C_OpenSession bad args.
 *
 */
void test_pkcs11_C_OpenSessionBadArgs( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = 0;
    CK_FLAGS xFlags = CKF_SERIAL_SESSION | CKF_RW_SESSION;

    xResult = prvInitializePkcs11();
    TEST_ASSERT_EQUAL( CKR_OK, xResult );

    if( TEST_PROTECT() )
    {
        xResult = C_OpenSession( 0, xFlags, NULL, 0, NULL );
        TEST_ASSERT_EQUAL( CKR_ARGUMENTS_BAD, xResult );

        xResult = C_OpenSession( 0, CKF_RW_SESSION, NULL, 0, &xSession );
        TEST_ASSERT_EQUAL( CKR_SESSION_PARALLEL_NOT_SUPPORTED, xResult );
    }

    xResult = prvUninitializePkcs11();
    TEST_ASSERT_EQUAL( CKR_OK, xResult );
}

/*!
 * @brief C_OpenSession Unable to acquire mutex.
 *
 */
void test_pkcs11_C_OpenSession_UnaquiredMutex( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = 0;
    CK_FLAGS xFlags = CKF_SERIAL_SESSION | CKF_RW_SESSION;

    xResult = prvInitializePkcs11();
    TEST_ASSERT_EQUAL( CKR_OK, xResult );

    if( TEST_PROTECT() )
    {
        mbedtls_calloc_Stub( pvPkcs11CallocCb );
        mock_osal_mutex_lock_ExpectAnyArgsAndReturn( 1 );
        xResult = C_OpenSession( 0, xFlags, NULL, 0, &xSession );
        TEST_ASSERT_EQUAL( CKR_FUNCTION_FAILED, xResult );
    }

    xResult = prvUninitializePkcs11();
    TEST_ASSERT_EQUAL( CKR_OK, xResult );
}
/* ======================  TESTING C_CloseSession  ============================ */

/*!
 * @brief C_CloseSession happy path.
 *
 */
void test_pkcs11_C_CloseSession( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = 0;

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        xResult = prvCloseSession( &xSession );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );
    }

    xResult = prvUninitializePkcs11();
    TEST_ASSERT_EQUAL( CKR_OK, xResult );
}

/*!
 * @brief C_CloseSession PKCS #11 not initialized.
 *
 */
void test_pkcs11_C_CloseSessionUninit( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = 0;

    xResult = C_CloseSession( xSession );
    TEST_ASSERT_EQUAL( CKR_CRYPTOKI_NOT_INITIALIZED, xResult );
}

/*!
 * @brief C_CloseSession PKCS #11 invalid session.
 *
 */
void test_pkcs11_C_CloseSessionBadSession( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = 0;

    xResult = prvInitializePkcs11();
    TEST_ASSERT_EQUAL( CKR_OK, xResult );

    if( TEST_PROTECT() )
    {
        xResult = C_CloseSession( xSession );
        TEST_ASSERT_EQUAL( CKR_SESSION_HANDLE_INVALID, xResult );
    }

    xResult = prvUninitializePkcs11();
    TEST_ASSERT_EQUAL( CKR_OK, xResult );
}
/* ======================  TESTING C_Login  ============================ */

/*!
 * @brief C_Login happy path.
 *
 * @note This test will need to be updated if support is added for C_Login.
 *
 */
void test_pkcs11_C_Login( void )
{
    CK_RV xResult = CKR_OK;

    xResult = C_Login( 0, 0, NULL, 0 );
    TEST_ASSERT_EQUAL( CKR_OK, xResult );
}

/* ======================  TESTING C_CreateObject  ============================ */

/*!
 * @brief C_CreateObject Creating an EC private key happy path.
 *
 */
void test_pkcs11_C_CreateObjectECPrivKey( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = 0;
    CK_KEY_TYPE xPrivateKeyType = CKK_EC;
    CK_OBJECT_CLASS xPrivateKeyClass = CKO_PRIVATE_KEY;
    CK_BBOOL xTrue = CK_TRUE;
    mbedtls_ecp_keypair xKeyContext = { 0 };
    char * pucPrivLabel = pkcs11configLABEL_DEVICE_PRIVATE_KEY_FOR_TLS;
    /* DER-encoding of an ANSI X9.62 Parameters value */
    CK_BYTE * pxEcPrivParams = ( CK_BYTE * ) ( "\x06\x08" MBEDTLS_OID_EC_GRP_SECP256R1 );
    CK_OBJECT_HANDLE xObject = 0;
    const uint8_t pusEmptyPubKey[ 6 ] = { 0xa1, 0x04, 0x03, 0x02, 0x00, 0x00 };
    uint8_t pusFakePrivateKey[ pkcs11_PRIVATE_EC_PRIME_256_DER_SIZE ] = { 0 };

    ( void ) memcpy( &pusFakePrivateKey[ pkcs11_PRIVATE_EC_PRIME_256_DER_SIZE - sizeof( pusEmptyPubKey ) ], pusEmptyPubKey, sizeof( pusEmptyPubKey ) );


    /* Private value D. */
    CK_BYTE pxD[ EC_D_LENGTH ] = { 0 };

    CK_ATTRIBUTE xPrivateKeyTemplate[] = EC_PRIV_KEY_INITIALIZER;

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        mbedtls_pk_init_CMockIgnore();
        mbedtls_calloc_Stub( pvPkcs11CallocCb );
        PKCS11_PAL_FindObject_IgnoreAndReturn( 1 );
        PKCS11_PAL_GetObjectValue_IgnoreAndReturn( CKR_OK );
        mbedtls_pk_parse_key_IgnoreAndReturn( 0 );
        PKCS11_PAL_GetObjectValueCleanup_CMockIgnore();
        mbedtls_calloc_IgnoreAndReturn( &xKeyContext );
        mbedtls_ecp_keypair_init_CMockIgnore();
        mbedtls_ecp_group_init_CMockIgnore();
        mbedtls_ecp_group_load_IgnoreAndReturn( 0 );
        mbedtls_calloc_Stub( pvPkcs11CallocCb );
        mbedtls_mpi_read_binary_IgnoreAndReturn( 0 );
        mbedtls_pk_write_key_der_ExpectAnyArgsAndReturn( 6 );
        mbedtls_pk_write_key_der_ReturnArrayThruPtr_buf( pusFakePrivateKey, sizeof( pusFakePrivateKey ) );
        mbedtls_pk_free_CMockIgnore();
        PKCS11_PAL_SaveObject_IgnoreAndReturn( 1 );
        mock_osal_mutex_lock_IgnoreAndReturn( 0 );
        mock_osal_mutex_unlock_IgnoreAndReturn( 0 );
        mbedtls_free_Stub( vPkcs11FreeCb );
        xResult = C_CreateObject( xSession,
                                  ( CK_ATTRIBUTE_PTR ) &xPrivateKeyTemplate,
                                  sizeof( xPrivateKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                                  &xObject );

        TEST_ASSERT_EQUAL( CKR_OK, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}

/*!
 * @brief C_CreateObject fail to malloc memory when loading EC curve.
 *
 */
void test_pkcs11_C_CreateObjectECCurveLoadFail( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = 0;
    CK_KEY_TYPE xPrivateKeyType = CKK_EC;
    CK_OBJECT_CLASS xPrivateKeyClass = CKO_PRIVATE_KEY;
    CK_BBOOL xTrue = CK_TRUE;
    mbedtls_ecp_keypair xKeyContext = { 0 };
    char * pucPrivLabel = pkcs11configLABEL_DEVICE_PRIVATE_KEY_FOR_TLS;
    /* DER-encoding of an ANSI X9.62 Parameters value */
    CK_BYTE * pxEcPrivParams = ( CK_BYTE * ) ( "\x06\x08" MBEDTLS_OID_EC_GRP_SECP256R1 );
    CK_OBJECT_HANDLE xObject = 0;
    const uint8_t pusEmptyPubKey[ 6 ] = { 0xa1, 0x04, 0x03, 0x02, 0x00, 0x00 };
    uint8_t pusFakePrivateKey[ pkcs11_PRIVATE_EC_PRIME_256_DER_SIZE ] = { 0 };

    ( void ) memcpy( &pusFakePrivateKey[ pkcs11_PRIVATE_EC_PRIME_256_DER_SIZE - sizeof( pusEmptyPubKey ) ], pusEmptyPubKey, sizeof( pusEmptyPubKey ) );


    /* Private value D. */
    CK_BYTE pxD[ EC_D_LENGTH ] = { 0 };

    CK_ATTRIBUTE xPrivateKeyTemplate[] = EC_PRIV_KEY_INITIALIZER;

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        mbedtls_pk_init_CMockIgnore();
        PKCS11_PAL_FindObject_IgnoreAndReturn( 0 );
        mbedtls_calloc_IgnoreAndReturn( NULL );
        mbedtls_pk_free_CMockIgnore();
        vPkcs11Free_Stub( vPkcs11FreeCb );
        mbedtls_free_Stub( vPkcs11FreeCb );
        xResult = C_CreateObject( xSession,
                                  ( CK_ATTRIBUTE_PTR ) &xPrivateKeyTemplate,
                                  sizeof( xPrivateKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                                  &xObject );

        TEST_ASSERT_EQUAL( CKR_HOST_MEMORY, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}

/*
 *!
 * @brief C_CreateObject Creating an EC private key attribute failures.
 *
 */
void test_pkcs11_C_CreateObjectECPrivKeyBadAtt( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = 0;
    CK_KEY_TYPE xPrivateKeyType = CKK_EC;
    CK_OBJECT_CLASS xPrivateKeyClass = CKO_PRIVATE_KEY;
    CK_BBOOL xTrue = CK_TRUE;
    CK_BBOOL xFalse = CK_FALSE;
    char * pucPrivLabel = pkcs11configLABEL_DEVICE_PRIVATE_KEY_FOR_TLS;
    /* DER-encoding of an ANSI X9.62 Parameters value */
    CK_BYTE * pxEcPrivParams = ( CK_BYTE * ) ( "\x06\x08" MBEDTLS_OID_EC_GRP_SECP256R1 );
    CK_OBJECT_HANDLE xObject = 0;

    /* Private value D. */
    CK_BYTE pxD[ EC_D_LENGTH ] = { 0 };

    CK_ATTRIBUTE xPrivateKeyTemplate[] = EC_PRIV_KEY_INITIALIZER;

    xPrivateKeyTemplate[ 5 ].type = CKA_MODULUS;

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        mbedtls_pk_init_CMockIgnore();
        mbedtls_calloc_Stub( pvPkcs11CallocCb );
        PKCS11_PAL_FindObject_IgnoreAndReturn( 1 );
        PKCS11_PAL_GetObjectValue_IgnoreAndReturn( CKR_OK );
        mbedtls_pk_parse_key_IgnoreAndReturn( 0 );
        PKCS11_PAL_GetObjectValueCleanup_CMockIgnore();
        mbedtls_pk_free_CMockIgnore();
        vPkcs11Free_Stub( vPkcs11FreeCb );
        mbedtls_free_Stub( vPkcs11FreeCb );
        xResult = C_CreateObject( xSession,
                                  ( CK_ATTRIBUTE_PTR ) &xPrivateKeyTemplate,
                                  sizeof( xPrivateKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                                  &xObject );

        TEST_ASSERT_EQUAL( CKR_ATTRIBUTE_TYPE_INVALID, xResult );

        xPrivateKeyTemplate[ 4 ].pValue = &xFalse;
        xPrivateKeyTemplate[ 5 ].type = CKA_EC_PARAMS;
        xResult = C_CreateObject( xSession,
                                  ( CK_ATTRIBUTE_PTR ) &xPrivateKeyTemplate,
                                  sizeof( xPrivateKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                                  &xObject );

        TEST_ASSERT_EQUAL( CKR_ATTRIBUTE_VALUE_INVALID, xResult );

        xPrivateKeyTemplate[ 4 ].pValue = &xTrue;
        mbedtls_mpi_read_binary_IgnoreAndReturn( -1 );
        xResult = C_CreateObject( xSession,
                                  ( CK_ATTRIBUTE_PTR ) &xPrivateKeyTemplate,
                                  sizeof( xPrivateKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                                  &xObject );
        TEST_ASSERT_EQUAL( CKR_FUNCTION_FAILED, xResult );

        xPrivateKeyTemplate[ 3 ].pValue = &xFalse;
        mbedtls_mpi_read_binary_IgnoreAndReturn( 0 );
        xResult = C_CreateObject( xSession,
                                  ( CK_ATTRIBUTE_PTR ) &xPrivateKeyTemplate,
                                  sizeof( xPrivateKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                                  &xObject );
        TEST_ASSERT_EQUAL( CKR_ATTRIBUTE_VALUE_INVALID, xResult );

        xPrivateKeyTemplate[ 3 ].pValue = &xTrue;
        xPrivateKeyTemplate[ 2 ].type = CKA_SIGN;
        xResult = C_CreateObject( xSession,
                                  ( CK_ATTRIBUTE_PTR ) &xPrivateKeyTemplate,
                                  sizeof( xPrivateKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                                  &xObject );
        TEST_ASSERT_EQUAL( CKR_ARGUMENTS_BAD, xResult );

        xPrivateKeyTemplate[ 2 ].type = CKA_LABEL;
        xPrivateKeyTemplate[ 5 ].pValue = pucPrivLabel;
        xResult = C_CreateObject( xSession,
                                  ( CK_ATTRIBUTE_PTR ) &xPrivateKeyTemplate,
                                  sizeof( xPrivateKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                                  &xObject );

        TEST_ASSERT_EQUAL( CKR_TEMPLATE_INCONSISTENT, xResult );


        mbedtls_pk_parse_key_IgnoreAndReturn( -1 );
        mbedtls_ecp_keypair_init_CMockIgnore();
        mbedtls_ecp_group_init_CMockIgnore();
        mbedtls_ecp_group_load_IgnoreAndReturn( -1 );
        mbedtls_pk_free_Stub( vMbedPkFree );
        xResult = C_CreateObject( xSession,
                                  ( CK_ATTRIBUTE_PTR ) &xPrivateKeyTemplate,
                                  sizeof( xPrivateKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                                  &xObject );
        TEST_ASSERT_EQUAL( CKR_FUNCTION_FAILED, xResult );


        xPrivateKeyType = CKK_RSA;
        mbedtls_pk_init_ExpectAnyArgs();
        mbedtls_rsa_init_CMockIgnore();
        mbedtls_calloc_IgnoreAndReturn( NULL );
        xResult = C_CreateObject( xSession,
                                  ( CK_ATTRIBUTE_PTR ) &xPrivateKeyTemplate,
                                  sizeof( xPrivateKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                                  &xObject );
        TEST_ASSERT_EQUAL( CKR_HOST_MEMORY, xResult );

        xPrivateKeyType = -1;
        xResult = C_CreateObject( xSession,
                                  ( CK_ATTRIBUTE_PTR ) &xPrivateKeyTemplate,
                                  sizeof( xPrivateKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                                  &xObject );
        TEST_ASSERT_EQUAL( CKR_MECHANISM_INVALID, xResult );

        xPrivateKeyType = CKK_EC;
        mbedtls_calloc_Stub( pvPkcs11CallocCb );
        mbedtls_ecp_group_load_IgnoreAndReturn( 0 );
        xPrivateKeyTemplate[ 4 ].type = CKA_VERIFY;
        xPrivateKeyTemplate[ 4 ].pValue = &xTrue;
        xPrivateKeyTemplate[ 4 ].ulValueLen = sizeof( CK_BBOOL );
        xResult = C_CreateObject( xSession,
                                  ( CK_ATTRIBUTE_PTR ) &xPrivateKeyTemplate,
                                  sizeof( xPrivateKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                                  &xObject );
        TEST_ASSERT_EQUAL( CKR_ATTRIBUTE_VALUE_INVALID, xResult );


        xResult = C_CreateObject( xSession,
                                  NULL,
                                  sizeof( xPrivateKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                                  &xObject );
        TEST_ASSERT_EQUAL( CKR_ARGUMENTS_BAD, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}

/*
 *!
 * @brief C_CreateObject Creating an EC private key fails when saving to DER.
 *
 */
void test_pkcs11_C_CreateObjectECPrivKeyDerFail( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = 0;
    CK_KEY_TYPE xPrivateKeyType = CKK_EC;
    CK_OBJECT_CLASS xPrivateKeyClass = CKO_PRIVATE_KEY;
    CK_BBOOL xTrue = CK_TRUE;
    mbedtls_ecp_keypair xKeyContext = { 0 };
    char * pucPrivLabel = pkcs11configLABEL_DEVICE_PRIVATE_KEY_FOR_TLS;
    /* DER-encoding of an ANSI X9.62 Parameters value */
    CK_BYTE * pxEcPrivParams = ( CK_BYTE * ) ( "\x06\x08" MBEDTLS_OID_EC_GRP_SECP256R1 );
    CK_OBJECT_HANDLE xObject = 0;

    /* Private value D. */
    CK_BYTE pxD[ EC_D_LENGTH ] = { 0 };

    CK_ATTRIBUTE xPrivateKeyTemplate[] = EC_PRIV_KEY_INITIALIZER;

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        mbedtls_pk_init_CMockIgnore();
        mbedtls_calloc_Stub( pvPkcs11CallocCb );
        PKCS11_PAL_FindObject_IgnoreAndReturn( 1 );
        PKCS11_PAL_GetObjectValue_IgnoreAndReturn( CKR_OK );
        mbedtls_pk_parse_key_IgnoreAndReturn( 0 );
        PKCS11_PAL_GetObjectValueCleanup_CMockIgnore();
        mbedtls_calloc_IgnoreAndReturn( &xKeyContext );
        mbedtls_ecp_keypair_init_CMockIgnore();
        mbedtls_ecp_group_init_CMockIgnore();
        mbedtls_ecp_group_load_IgnoreAndReturn( 0 );
        mbedtls_mpi_read_binary_IgnoreAndReturn( 0 );
        mbedtls_calloc_Stub( pvPkcs11CallocCb );
        mbedtls_pk_write_key_der_IgnoreAndReturn( -1 );
        mbedtls_pk_free_CMockIgnore();
        PKCS11_PAL_SaveObject_IgnoreAndReturn( 1 );
        vPkcs11Free_Stub( vPkcs11FreeCb );
        mbedtls_free_Stub( vPkcs11FreeCb );
        xResult = C_CreateObject( xSession,
                                  ( CK_ATTRIBUTE_PTR ) &xPrivateKeyTemplate,
                                  sizeof( xPrivateKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                                  &xObject );

        TEST_ASSERT_EQUAL( CKR_FUNCTION_FAILED, xResult );

        /* Malloc fails in prvSaveDerKeyToPal */
        mbedtls_calloc_Stub( pvPkcs11CallocCb );
        mbedtls_calloc_IgnoreAndReturn( NULL );
        mbedtls_pk_write_key_der_IgnoreAndReturn( 1 );
        xResult = C_CreateObject( xSession,
                                  ( CK_ATTRIBUTE_PTR ) &xPrivateKeyTemplate,
                                  sizeof( xPrivateKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                                  &xObject );

        TEST_ASSERT_EQUAL( CKR_HOST_MEMORY, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}

/*!
 * @brief C_CreateObject Creating an EC public key happy path.
 *
 */
void test_pkcs11_C_CreateObjectECPubKey( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = 0;
    CK_KEY_TYPE xPublicKeyType = CKK_EC;
    CK_OBJECT_CLASS xPublicKeyClass = CKO_PUBLIC_KEY;
    CK_BBOOL xTrue = CK_TRUE;
    char * pucPubLabel = pkcs11configLABEL_DEVICE_PUBLIC_KEY_FOR_TLS;
    size_t xLength = 256;
    /* DER-encoding of an ANSI X9.62 Parameters value */
    CK_BYTE pxEcPubParams[] = pkcs11DER_ENCODED_OID_P256;
    CK_OBJECT_HANDLE xObject = 0;

    CK_BYTE pxEcPoint[ 256 ] = { 0 };

    CK_ATTRIBUTE xPublicKeyTemplate[] = EC_PUB_KEY_INITIALIZER;

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        mbedtls_pk_init_CMockIgnore();
        mbedtls_calloc_Stub( pvPkcs11CallocCb );
        PKCS11_PAL_FindObject_IgnoreAndReturn( CK_INVALID_HANDLE );
        mbedtls_pk_parse_public_key_IgnoreAndReturn( 0 );
        PKCS11_PAL_GetObjectValueCleanup_CMockIgnore();
        mbedtls_ecp_keypair_init_CMockIgnore();
        mbedtls_ecp_group_init_CMockIgnore();
        mbedtls_ecp_group_load_IgnoreAndReturn( 0 );
        mbedtls_ecp_point_read_binary_IgnoreAndReturn( 0 );
        mbedtls_mpi_read_binary_IgnoreAndReturn( 0 );
        mbedtls_pk_write_pubkey_der_IgnoreAndReturn( 1 );
        mbedtls_pk_free_Stub( vMbedPkFree );
        PKCS11_PAL_SaveObject_IgnoreAndReturn( 1 );
        mock_osal_mutex_lock_IgnoreAndReturn( 0 );
        mock_osal_mutex_unlock_IgnoreAndReturn( 0 );
        vPkcs11Free_Stub( vPkcs11FreeCb );
        mbedtls_free_Stub( vPkcs11FreeCb );
        xResult = C_CreateObject( xSession,
                                  ( CK_ATTRIBUTE_PTR ) &xPublicKeyTemplate,
                                  sizeof( xPublicKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                                  &xObject );

        TEST_ASSERT_EQUAL( CKR_OK, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}

/*!
 * @brief C_CreateObject Creating an EC public key fails when saving in PAL.
 *
 */
void test_pkcs11_C_CreateObjectECPubKeyPalSaveFail( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = 0;
    CK_KEY_TYPE xPublicKeyType = CKK_EC;
    CK_OBJECT_CLASS xPublicKeyClass = CKO_PUBLIC_KEY;
    CK_BBOOL xTrue = CK_TRUE;
    char * pucPubLabel = pkcs11configLABEL_DEVICE_PUBLIC_KEY_FOR_TLS;
    size_t xLength = 256;
    /* DER-encoding of an ANSI X9.62 Parameters value */
    CK_BYTE pxEcPubParams[] = pkcs11DER_ENCODED_OID_P256;
    CK_OBJECT_HANDLE xObject = 0;

    CK_BYTE pxEcPoint[ 256 ] = { 0 };

    CK_ATTRIBUTE xPublicKeyTemplate[] = EC_PUB_KEY_INITIALIZER;

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        mbedtls_pk_init_CMockIgnore();
        mbedtls_calloc_Stub( pvPkcs11CallocCb );
        PKCS11_PAL_FindObject_IgnoreAndReturn( CK_INVALID_HANDLE );
        mbedtls_pk_parse_public_key_IgnoreAndReturn( 0 );
        PKCS11_PAL_GetObjectValueCleanup_CMockIgnore();
        mbedtls_ecp_keypair_init_CMockIgnore();
        mbedtls_ecp_group_init_CMockIgnore();
        mbedtls_ecp_group_load_IgnoreAndReturn( 0 );
        mbedtls_ecp_point_read_binary_IgnoreAndReturn( 0 );
        mbedtls_mpi_read_binary_IgnoreAndReturn( 0 );
        mbedtls_pk_write_pubkey_der_IgnoreAndReturn( 1 );
        mbedtls_pk_free_Stub( vMbedPkFree );
        PKCS11_PAL_SaveObject_IgnoreAndReturn( 0 );
        mock_osal_mutex_lock_IgnoreAndReturn( 0 );
        mock_osal_mutex_unlock_IgnoreAndReturn( 0 );
        vPkcs11Free_Stub( vPkcs11FreeCb );
        mbedtls_free_Stub( vPkcs11FreeCb );
        xResult = C_CreateObject( xSession,
                                  ( CK_ATTRIBUTE_PTR ) &xPublicKeyTemplate,
                                  sizeof( xPublicKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                                  &xObject );

        TEST_ASSERT_EQUAL( CKR_DEVICE_MEMORY, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}

/*
 *!
 * @brief C_CreateObject Creating an EC public key attribute failures.
 *
 */
void test_pkcs11_C_CreateObjectECPubKeyBadAtt( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = 0;
    CK_KEY_TYPE xPublicKeyType = CKK_EC;
    CK_KEY_TYPE xFaultyPublicKeyType = CKK_AES;
    CK_OBJECT_CLASS xPublicKeyClass = CKO_PUBLIC_KEY;
    CK_BBOOL xTrue = CK_TRUE;
    CK_BBOOL xFalse = CK_FALSE;
    char * pucPubLabel = pkcs11configLABEL_DEVICE_PUBLIC_KEY_FOR_TLS;
    size_t xLength = pkcs11EC_POINT_LENGTH;
    /* DER-encoding of an ANSI X9.62 Parameters value */
    CK_BYTE pxEcPubParams[] = pkcs11DER_ENCODED_OID_P256;
    CK_OBJECT_HANDLE xObject = 0;
    CK_BYTE pxEcPoint[ pkcs11EC_POINT_LENGTH ] = { 0 };

    CK_ATTRIBUTE xPublicKeyTemplate[] = EC_PUB_KEY_INITIALIZER;

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        xPublicKeyTemplate[ 5 ].type = CKA_MODULUS;

        mbedtls_pk_init_CMockIgnore();
        mbedtls_calloc_Stub( pvPkcs11CallocCb );
        PKCS11_PAL_FindObject_IgnoreAndReturn( 1 );
        PKCS11_PAL_GetObjectValue_IgnoreAndReturn( CKR_OK );
        mbedtls_pk_parse_public_key_IgnoreAndReturn( 0 );
        PKCS11_PAL_GetObjectValueCleanup_CMockIgnore();
        mbedtls_pk_free_CMockIgnore();
        vPkcs11Free_Stub( vPkcs11FreeCb );
        mbedtls_free_Stub( vPkcs11FreeCb );
        xResult = C_CreateObject( xSession,
                                  ( CK_ATTRIBUTE_PTR ) &xPublicKeyTemplate,
                                  sizeof( xPublicKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                                  &xObject );

        TEST_ASSERT_EQUAL( CKR_ATTRIBUTE_TYPE_INVALID, xResult );

        xPublicKeyTemplate[ 1 ].pValue = &xFaultyPublicKeyType;
        xResult = C_CreateObject( xSession,
                                  ( CK_ATTRIBUTE_PTR ) &xPublicKeyTemplate,
                                  sizeof( xPublicKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                                  &xObject );

        TEST_ASSERT_EQUAL( CKR_MECHANISM_INVALID, xResult );

        /* Reuse the variable. The goal being to pass a bad attribute class to
         * C_CreateObject */
        xPublicKeyTemplate[ 0 ].pValue = &xFaultyPublicKeyType;
        xPublicKeyTemplate[ 1 ].pValue = &xPublicKeyType;
        xResult = C_CreateObject( xSession,
                                  ( CK_ATTRIBUTE_PTR ) &xPublicKeyTemplate,
                                  sizeof( xPublicKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                                  &xObject );

        TEST_ASSERT_EQUAL( CKR_ATTRIBUTE_VALUE_INVALID, xResult );

        xPublicKeyTemplate[ 0 ].type = CKA_KEY_TYPE;
        xResult = C_CreateObject( xSession,
                                  ( CK_ATTRIBUTE_PTR ) &xPublicKeyTemplate,
                                  sizeof( xPublicKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                                  &xObject );

        TEST_ASSERT_EQUAL( CKR_TEMPLATE_INCOMPLETE, xResult );
        xPublicKeyTemplate[ 0 ].type = CKA_CLASS;
        xPublicKeyTemplate[ 0 ].pValue = &xPublicKeyClass;

        xPublicKeyTemplate[ 5 ].type = CKA_EC_POINT;
        xPublicKeyTemplate[ 5 ].ulValueLen = 0;
        xResult = C_CreateObject( xSession,
                                  ( CK_ATTRIBUTE_PTR ) &xPublicKeyTemplate,
                                  sizeof( xPublicKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                                  &xObject );
        TEST_ASSERT_EQUAL( CKR_ATTRIBUTE_VALUE_INVALID, xResult );
        xPublicKeyTemplate[ 5 ].ulValueLen = xLength;

        xPublicKeyTemplate[ 3 ].pValue = &xFalse;
        xResult = C_CreateObject( xSession,
                                  ( CK_ATTRIBUTE_PTR ) &xPublicKeyTemplate,
                                  sizeof( xPublicKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                                  &xObject );
        TEST_ASSERT_EQUAL( CKR_ATTRIBUTE_VALUE_INVALID, xResult );
        xPublicKeyTemplate[ 5 ].ulValueLen = xLength;


        xPublicKeyTemplate[ 3 ].type = CKA_SIGN;
        xResult = C_CreateObject( xSession,
                                  ( CK_ATTRIBUTE_PTR ) &xPublicKeyTemplate,
                                  sizeof( xPublicKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                                  &xObject );
        TEST_ASSERT_EQUAL( CKR_ATTRIBUTE_VALUE_INVALID, xResult );

        xPublicKeyTemplate[ 3 ].type = CKA_VERIFY;
        xPublicKeyTemplate[ 3 ].pValue = &xTrue;
        mbedtls_ecp_point_read_binary_IgnoreAndReturn( -1 );
        xResult = C_CreateObject( xSession,
                                  ( CK_ATTRIBUTE_PTR ) &xPublicKeyTemplate,
                                  sizeof( xPublicKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                                  &xObject );

        TEST_ASSERT_EQUAL( CKR_FUNCTION_FAILED, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}

/*
 *!
 * @brief C_CreateObject Creating an RSA Private key happy path.
 *
 */
void test_pkcs11_C_CreateObjectRSAPrivKey( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = 0;
    CK_KEY_TYPE xPrivateKeyType = CKK_RSA;
    CK_OBJECT_CLASS xPrivateKeyClass = CKO_PRIVATE_KEY;
    CK_BBOOL xTrue = CK_TRUE;
    char * pucLabel = pkcs11configLABEL_DEVICE_PRIVATE_KEY_FOR_TLS;
    CK_OBJECT_HANDLE xObject = 0;

    RsaParams_t xRsaParams = { 0 };

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        CK_ATTRIBUTE xPrivateKeyTemplate[] = RSA_PRIV_KEY_INITIALIZER;

        mbedtls_pk_init_CMockIgnore();
        mbedtls_calloc_Stub( pvPkcs11CallocCb );
        mbedtls_rsa_init_CMockIgnore();
        mbedtls_rsa_import_raw_IgnoreAndReturn( 0 );
        mbedtls_mpi_read_binary_IgnoreAndReturn( 0 );
        mbedtls_pk_write_key_der_IgnoreAndReturn( 1 );
        mbedtls_pk_free_Stub( vMbedPkFree );
        PKCS11_PAL_SaveObject_IgnoreAndReturn( 1 );
        mock_osal_mutex_lock_IgnoreAndReturn( 0 );
        mock_osal_mutex_unlock_IgnoreAndReturn( 0 );
        vPkcs11Free_Stub( vPkcs11FreeCb );
        mbedtls_free_Stub( vPkcs11FreeCb );
        xResult = C_CreateObject( xSession,
                                  ( CK_ATTRIBUTE_PTR ) &xPrivateKeyTemplate,
                                  sizeof( xPrivateKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                                  &xObject );

        TEST_ASSERT_EQUAL( CKR_OK, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}

/*
 *!
 * @brief C_CreateObject Creating an RSA private key attribute failures.
 *
 */
void test_pkcs11_C_CreateObjectRSAPrivKeyBadAtt( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = 0;
    CK_KEY_TYPE xPrivateKeyType = CKK_RSA;
    CK_OBJECT_CLASS xPrivateKeyClass = CKO_PRIVATE_KEY;
    CK_BBOOL xTrue = CK_TRUE;
    CK_BBOOL xFalse = CK_FALSE;
    char * pucLabel = pkcs11configLABEL_DEVICE_PRIVATE_KEY_FOR_TLS;
    CK_OBJECT_HANDLE xObject = 0;

    RsaParams_t xRsaParams = { 0 };

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        CK_ATTRIBUTE xPrivateKeyTemplate[] = RSA_PRIV_KEY_INITIALIZER;
        xPrivateKeyTemplate[ 4 ].type = CKA_EC_POINT;

        mbedtls_pk_init_CMockIgnore();
        mbedtls_calloc_Stub( pvPkcs11CallocCb );
        mbedtls_rsa_init_CMockIgnore();
        mbedtls_pk_free_Stub( vMbedPkFree );
        vPkcs11Free_Stub( vPkcs11FreeCb );
        mbedtls_free_Stub( vPkcs11FreeCb );
        xResult = C_CreateObject( xSession,
                                  ( CK_ATTRIBUTE_PTR ) &xPrivateKeyTemplate,
                                  sizeof( xPrivateKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                                  &xObject );

        TEST_ASSERT_EQUAL( CKR_ATTRIBUTE_TYPE_INVALID, xResult );

        xPrivateKeyTemplate[ 4 ].type = CKA_SIGN;
        xPrivateKeyTemplate[ 4 ].pValue = &xFalse;
        xResult = C_CreateObject( xSession,
                                  ( CK_ATTRIBUTE_PTR ) &xPrivateKeyTemplate,
                                  sizeof( xPrivateKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                                  &xObject );

        TEST_ASSERT_EQUAL( CKR_ATTRIBUTE_VALUE_INVALID, xResult );

        xPrivateKeyTemplate[ 4 ].type = CKA_VERIFY;
        xResult = C_CreateObject( xSession,
                                  ( CK_ATTRIBUTE_PTR ) &xPrivateKeyTemplate,
                                  sizeof( xPrivateKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                                  &xObject );
        TEST_ASSERT_EQUAL( CKR_ATTRIBUTE_VALUE_INVALID, xResult );
        xPrivateKeyTemplate[ 4 ].type = CKA_SIGN;

        xTrue = CK_FALSE;
        xPrivateKeyTemplate[ 2 ].type = CKA_EC_POINT;
        xResult = C_CreateObject( xSession,
                                  ( CK_ATTRIBUTE_PTR ) &xPrivateKeyTemplate,
                                  sizeof( xPrivateKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                                  &xObject );

        TEST_ASSERT_EQUAL( CKR_ARGUMENTS_BAD, xResult );

        xPrivateKeyTemplate[ 2 ].type = CKA_LABEL;
        xTrue = CK_TRUE;
        mbedtls_rsa_import_raw_IgnoreAndReturn( 1 );
        xResult = C_CreateObject( xSession,
                                  ( CK_ATTRIBUTE_PTR ) &xPrivateKeyTemplate,
                                  sizeof( xPrivateKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                                  &xObject );

        TEST_ASSERT_EQUAL( CKR_ATTRIBUTE_VALUE_INVALID, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}

/*
 *!
 * @brief C_CreateObject Creating an RSA Public key happy path.
 */
void test_pkcs11_C_CreateObjectRSAPubKey( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = CK_INVALID_HANDLE;
    CK_KEY_TYPE xPublicKeyType = CKK_RSA;
    CK_OBJECT_CLASS xClass = CKO_PUBLIC_KEY;
    CK_OBJECT_HANDLE xObject = CK_INVALID_HANDLE;
    CK_BBOOL xTrue = CK_TRUE;
    CK_BYTE xPublicExponent[] = { 0x01, 0x00, 0x01 };
    CK_BYTE xModulus[ MODULUS_LENGTH + 1 ] = { 0 };
    CK_BYTE pucPublicKeyLabel[] = pkcs11configLABEL_DEVICE_PUBLIC_KEY_FOR_TLS;

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        CK_ATTRIBUTE xPublicKeyTemplate[] =
        {
            { CKA_CLASS,           &xClass,           sizeof( CK_OBJECT_CLASS )                    },
            { CKA_KEY_TYPE,        &xPublicKeyType,   sizeof( CK_KEY_TYPE )                        },
            { CKA_TOKEN,           &xTrue,            sizeof( xTrue )                              },
            { CKA_MODULUS,         &xModulus + 1,     MODULUS_LENGTH                               },
            { CKA_VERIFY,          &xTrue,            sizeof( xTrue )                              },
            { CKA_PUBLIC_EXPONENT, xPublicExponent,   sizeof( xPublicExponent )                    },
            { CKA_LABEL,           pucPublicKeyLabel, strlen( ( const char * ) pucPublicKeyLabel ) }
        };

        mbedtls_pk_init_CMockIgnore();
        mbedtls_calloc_Stub( pvPkcs11CallocCb );
        mbedtls_rsa_init_CMockIgnore();
        mbedtls_rsa_import_raw_IgnoreAndReturn( 0 );
        mbedtls_pk_write_pubkey_der_IgnoreAndReturn( 1 );
        mbedtls_pk_free_Stub( vMbedPkFree );
        PKCS11_PAL_SaveObject_IgnoreAndReturn( 1 );
        mock_osal_mutex_lock_IgnoreAndReturn( 0 );
        mock_osal_mutex_unlock_IgnoreAndReturn( 0 );
        vPkcs11Free_Stub( vPkcs11FreeCb );
        mbedtls_free_Stub( vPkcs11FreeCb );
        xResult = C_CreateObject( xSession,
                                  ( CK_ATTRIBUTE_PTR ) &xPublicKeyTemplate,
                                  sizeof( xPublicKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                                  &xObject );

        TEST_ASSERT_EQUAL( CKR_OK, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}

/*
 *!
 * @brief C_CreateObject Creating an RSA Public key mbed TLS failure.
 */
void test_pkcs11_C_CreateObjectRSAPubKeyMbedFail( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = CK_INVALID_HANDLE;
    CK_KEY_TYPE xPublicKeyType = CKK_RSA;
    CK_OBJECT_CLASS xClass = CKO_PUBLIC_KEY;
    CK_OBJECT_HANDLE xObject = CK_INVALID_HANDLE;
    CK_BBOOL xTrue = CK_TRUE;
    CK_BYTE xPublicExponent[] = { 0x01, 0x00, 0x01 };
    CK_BYTE xModulus[ MODULUS_LENGTH + 1 ] = { 0 };
    CK_BYTE pucPublicKeyLabel[] = pkcs11configLABEL_DEVICE_PUBLIC_KEY_FOR_TLS;

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        CK_ATTRIBUTE xPublicKeyTemplate[] =
        {
            { CKA_CLASS,           &xClass,           sizeof( CK_OBJECT_CLASS )                    },
            { CKA_KEY_TYPE,        &xPublicKeyType,   sizeof( CK_KEY_TYPE )                        },
            { CKA_TOKEN,           &xTrue,            sizeof( xTrue )                              },
            { CKA_MODULUS,         &xModulus + 1,     MODULUS_LENGTH                               },
            { CKA_VERIFY,          &xTrue,            sizeof( xTrue )                              },
            { CKA_PUBLIC_EXPONENT, xPublicExponent,   sizeof( xPublicExponent )                    },
            { CKA_LABEL,           pucPublicKeyLabel, strlen( ( const char * ) pucPublicKeyLabel ) }
        };

        mbedtls_pk_init_CMockIgnore();
        mbedtls_calloc_Stub( pvPkcs11CallocCb );
        mbedtls_rsa_init_CMockIgnore();
        mbedtls_rsa_import_raw_IgnoreAndReturn( -1 );
        mbedtls_pk_free_Stub( vMbedPkFree );
        mock_osal_mutex_lock_IgnoreAndReturn( 0 );
        mock_osal_mutex_unlock_IgnoreAndReturn( 0 );
        vPkcs11Free_Stub( vPkcs11FreeCb );
        mbedtls_free_Stub( vPkcs11FreeCb );
        xResult = C_CreateObject( xSession,
                                  ( CK_ATTRIBUTE_PTR ) &xPublicKeyTemplate,
                                  sizeof( xPublicKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                                  &xObject );

        TEST_ASSERT_EQUAL( CKR_FUNCTION_FAILED, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}

/*
 *!
 * @brief C_CreateObject Creating an RSA Public key bad attribute parameters.
 */
void test_pkcs11_C_CreateObjectRSAPubKeyBadAtts( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = CK_INVALID_HANDLE;
    CK_KEY_TYPE xPublicKeyType = CKK_RSA;
    CK_OBJECT_CLASS xClass = CKO_PUBLIC_KEY;
    CK_OBJECT_HANDLE xObject = CK_INVALID_HANDLE;
    CK_BBOOL xTrue = CK_TRUE;
    CK_BBOOL xFalse = CK_FALSE;
    CK_BYTE xPublicExponent[] = { 0x01, 0x00, 0x01 };
    CK_BYTE xModulus[ MODULUS_LENGTH + 1 ] = { 0 };
    CK_BYTE pucPublicKeyLabel[] = pkcs11configLABEL_DEVICE_PUBLIC_KEY_FOR_TLS;

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        CK_ATTRIBUTE xPublicKeyTemplate[] =
        {
            { CKA_CLASS,           &xClass,           sizeof( CK_OBJECT_CLASS )                    },
            { CKA_KEY_TYPE,        &xPublicKeyType,   sizeof( CK_KEY_TYPE )                        },
            { CKA_TOKEN,           &xTrue,            sizeof( xTrue )                              },
            { CKA_MODULUS,         &xModulus + 1,     MODULUS_LENGTH                               },
            { CKA_VERIFY,          &xFalse,           sizeof( xFalse )                             },
            { CKA_PUBLIC_EXPONENT, xPublicExponent,   sizeof( xPublicExponent )                    },
            { CKA_LABEL,           pucPublicKeyLabel, strlen( ( const char * ) pucPublicKeyLabel ) }
        };

        mbedtls_pk_init_CMockIgnore();
        mbedtls_calloc_Stub( pvPkcs11CallocCb );
        mbedtls_rsa_init_CMockIgnore();
        mbedtls_rsa_import_raw_IgnoreAndReturn( 0 );
        mbedtls_pk_write_pubkey_der_IgnoreAndReturn( 1 );
        mbedtls_pk_free_Stub( vMbedPkFree );
        PKCS11_PAL_SaveObject_IgnoreAndReturn( 1 );
        mock_osal_mutex_lock_IgnoreAndReturn( 0 );
        mock_osal_mutex_unlock_IgnoreAndReturn( 0 );
        vPkcs11Free_Stub( vPkcs11FreeCb );
        mbedtls_free_Stub( vPkcs11FreeCb );
        xResult = C_CreateObject( xSession, ( CK_ATTRIBUTE_PTR ) &xPublicKeyTemplate,
                                  sizeof( xPublicKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                                  &xObject );
        TEST_ASSERT_EQUAL( CKR_ATTRIBUTE_VALUE_INVALID, xResult );
        xPublicKeyTemplate[ 4 ].pValue = &xTrue;

        xPublicKeyTemplate[ 2 ].pValue = &xFalse;
        xResult = C_CreateObject( xSession, ( CK_ATTRIBUTE_PTR ) &xPublicKeyTemplate,
                                  sizeof( xPublicKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                                  &xObject );
        TEST_ASSERT_EQUAL( CKR_ATTRIBUTE_VALUE_INVALID, xResult );
        xPublicKeyTemplate[ 2 ].pValue = &xTrue;

        xPublicKeyTemplate[ 2 ].type = CKA_SIGN;
        xResult = C_CreateObject( xSession, ( CK_ATTRIBUTE_PTR ) &xPublicKeyTemplate,
                                  sizeof( xPublicKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                                  &xObject );
        TEST_ASSERT_EQUAL( CKR_ATTRIBUTE_VALUE_INVALID, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}

/*
 *!
 * @brief C_CreateObject Creating a Certificate happy path.
 *
 */
void test_pkcs11_C_CreateObjectCertificate( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = 0;
    CK_OBJECT_HANDLE xObject = 0;
    CK_OBJECT_CLASS xCertificateClass = CKO_CERTIFICATE;
    CK_CERTIFICATE_TYPE xCertificateType = CKC_X_509;
    CK_BBOOL xTokenStorage = CK_TRUE;
    CK_BYTE xSubject[] = "TestSubject";
    CK_BYTE xCert[] = "Empty Cert";
    char * pucLabel = pkcs11configLABEL_DEVICE_CERTIFICATE_FOR_TLS;

    PKCS11_CertificateTemplate_t xCertificateTemplate = CERT_INITIALIZER;

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        PKCS11_PAL_SaveObject_IgnoreAndReturn( 1 );
        xResult = C_CreateObject( xSession,
                                  ( CK_ATTRIBUTE_PTR ) &xCertificateTemplate,
                                  sizeof( xCertificateTemplate ) / sizeof( CK_ATTRIBUTE ),
                                  &xObject );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}

/*
 *!
 * @brief C_CreateObject Creating a Certificate fails when saving to PAL.
 *
 */
void test_pkcs11_C_CreateObjectCertificateSaveFail( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = 0;
    CK_OBJECT_HANDLE xObject = 0;
    CK_OBJECT_CLASS xCertificateClass = CKO_CERTIFICATE;
    CK_CERTIFICATE_TYPE xCertificateType = CKC_X_509;
    CK_BBOOL xTokenStorage = CK_TRUE;
    CK_BYTE xSubject[] = "TestSubject";
    CK_BYTE xCert[] = "Empty Cert";
    char * pucLabel = pkcs11configLABEL_DEVICE_CERTIFICATE_FOR_TLS;

    PKCS11_CertificateTemplate_t xCertificateTemplate = CERT_INITIALIZER;

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        PKCS11_PAL_SaveObject_IgnoreAndReturn( 0 );
        xResult = C_CreateObject( xSession,
                                  ( CK_ATTRIBUTE_PTR ) &xCertificateTemplate,
                                  sizeof( xCertificateTemplate ) / sizeof( CK_ATTRIBUTE ),
                                  &xObject );
        TEST_ASSERT_EQUAL( CKR_DEVICE_MEMORY, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}

/*
 *!
 * @brief C_CreateObject Creating a Certificate fails because the template is incomplete.
 *
 */
void test_pkcs11_C_CreateObjectCertificateIncomplete( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = 0;
    CK_OBJECT_HANDLE xObject = 0;
    CK_OBJECT_CLASS xCertificateClass = CKO_CERTIFICATE;
    CK_CERTIFICATE_TYPE xCertificateType = CKC_X_509;
    CK_BBOOL xTokenStorage = CK_TRUE;
    CK_BYTE xSubject[] = "TestSubject";
    CK_BYTE xCert[] = "Empty Cert";
    char * pucLabel = pkcs11configLABEL_DEVICE_CERTIFICATE_FOR_TLS;

    CK_ATTRIBUTE xCertificateTemplate[] =
    {
        { CKA_CLASS, &xCertificateClass, sizeof( CK_OBJECT_CLASS ) },
    };

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        xResult = C_CreateObject( xSession,
                                  ( CK_ATTRIBUTE_PTR ) &xCertificateTemplate,
                                  sizeof( xCertificateTemplate ) / sizeof( CK_ATTRIBUTE ),
                                  &xObject );
        TEST_ASSERT_EQUAL( CKR_TEMPLATE_INCOMPLETE, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}


/*
 *!
 * @brief C_CreateObject Creating a Certificate with a label that is too long.
 *
 */
void test_pkcs11_C_CreateObjectCertificateTooLongLabel( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = 0;
    CK_OBJECT_HANDLE xObject = 0;
    CK_OBJECT_CLASS xCertificateClass = CKO_CERTIFICATE;
    CK_CERTIFICATE_TYPE xCertificateType = CKC_X_509;
    CK_BBOOL xTokenStorage = CK_TRUE;
    CK_BYTE xSubject[] = "TestSubject";
    CK_BYTE xCert[] = "Empty Cert";
    char * pucLabel = "TestTemporyaryCertificate123456789ABEF";

    PKCS11_CertificateTemplate_t xCertificateTemplate = CERT_INITIALIZER;

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        xResult = C_CreateObject( xSession,
                                  ( CK_ATTRIBUTE_PTR ) &xCertificateTemplate,
                                  sizeof( xCertificateTemplate ) / sizeof( CK_ATTRIBUTE ),
                                  &xObject );
        TEST_ASSERT_EQUAL( CKR_DATA_LEN_RANGE, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}

/*
 *!
 * @brief C_CreateObject Bad Certificate type.
 *
 */
void test_pkcs11_C_CreateObjectCertificateBadType( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = 0;
    CK_OBJECT_HANDLE xObject = 0;
    CK_OBJECT_CLASS xCertificateClass = CKO_CERTIFICATE;
    CK_CERTIFICATE_TYPE xCertificateType = -1;
    CK_BBOOL xTokenStorage = CK_TRUE;
    CK_BYTE xSubject[] = "TestSubject";
    CK_BYTE xCert[] = "Empty Cert";
    char * pucLabel = pkcs11configLABEL_DEVICE_CERTIFICATE_FOR_TLS;

    PKCS11_CertificateTemplate_t xCertificateTemplate = CERT_INITIALIZER;


    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        PKCS11_PAL_SaveObject_IgnoreAndReturn( 1 );
        PKCS11_PAL_GetObjectValueCleanup_Ignore();

        xResult = C_CreateObject( xSession,
                                  ( CK_ATTRIBUTE_PTR ) &xCertificateTemplate,
                                  sizeof( xCertificateTemplate ) / sizeof( CK_ATTRIBUTE ),
                                  &xObject );
        TEST_ASSERT_EQUAL( CKR_ATTRIBUTE_VALUE_INVALID, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}

/*
 *!
 * @brief C_CreateObject Bad Certificate token value.
 *
 */
void test_pkcs11_C_CreateObjectCertificateBadToken( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = 0;
    CK_OBJECT_HANDLE xObject = 0;
    CK_OBJECT_CLASS xCertificateClass = CKO_CERTIFICATE;
    CK_CERTIFICATE_TYPE xCertificateType = CKC_X_509;
    CK_BBOOL xTokenStorage = CK_FALSE;
    CK_BYTE xSubject[] = "TestSubject";
    CK_BYTE xCert[] = "Empty Cert";
    char * pucLabel = pkcs11configLABEL_DEVICE_CERTIFICATE_FOR_TLS;

    PKCS11_CertificateTemplate_t xCertificateTemplate = CERT_INITIALIZER;

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        PKCS11_PAL_SaveObject_IgnoreAndReturn( 1 );
        PKCS11_PAL_GetObjectValueCleanup_Ignore();
        xResult = C_CreateObject( xSession,
                                  ( CK_ATTRIBUTE_PTR ) &xCertificateTemplate,
                                  sizeof( xCertificateTemplate ) / sizeof( CK_ATTRIBUTE ),
                                  &xObject );
        TEST_ASSERT_EQUAL( CKR_ATTRIBUTE_VALUE_INVALID, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}

/*
 *!
 * @brief C_CreateObject Unknown Certificate Attribute.
 *
 */
void test_pkcs11_C_CreateObjectCertificateUnkownAtt( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = 0;
    CK_OBJECT_HANDLE xObject = 0;
    CK_OBJECT_CLASS xCertificateClass = CKO_CERTIFICATE;
    CK_CERTIFICATE_TYPE xCertificateType = CKC_X_509;
    CK_BBOOL xTokenStorage = CK_TRUE;
    CK_BYTE xSubject[] = "TestSubject";
    CK_BYTE xCert[] = "Empty Cert";
    char * pucLabel = pkcs11configLABEL_DEVICE_CERTIFICATE_FOR_TLS;

    PKCS11_CertificateTemplate_t xCertificateTemplate = CERT_INITIALIZER;

    xCertificateTemplate.xSubject.type = CKA_MODULUS;

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        PKCS11_PAL_SaveObject_IgnoreAndReturn( 1 );
        PKCS11_PAL_GetObjectValueCleanup_Ignore();
        xResult = C_CreateObject( xSession,
                                  ( CK_ATTRIBUTE_PTR ) &xCertificateTemplate,
                                  sizeof( xCertificateTemplate ) / sizeof( CK_ATTRIBUTE ),
                                  &xObject );
        TEST_ASSERT_EQUAL( CKR_ATTRIBUTE_TYPE_INVALID, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}

/*!
 * @brief C_CreateObject Creating a SHA256-HMAC secret key happy path.
 *
 */
void test_pkcs11_C_CreateObjectSHA256HMACKey( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = CK_INVALID_HANDLE;
    CK_KEY_TYPE xKeyType = CKK_SHA256_HMAC;
    CK_OBJECT_CLASS xKeyClass = CKO_SECRET_KEY;
    CK_BBOOL xTrue = CK_TRUE;
    CK_OBJECT_HANDLE xObject = CK_INVALID_HANDLE;
    CK_BYTE pcLabel[] = pkcs11configLABEL_HMAC_KEY;

    CK_BYTE pxKeyValue[] = "abcdabcdabcdabcdabcdabcdabcdabcd";

    CK_ATTRIBUTE xSHA256HMACTemplate[] =
    {
        { CKA_CLASS,    &xKeyClass, sizeof( CK_OBJECT_CLASS ) },
        { CKA_KEY_TYPE, &xKeyType,  sizeof( CK_KEY_TYPE )     },
        { CKA_LABEL,    pcLabel,    sizeof( pcLabel ) - 1     },
        { CKA_TOKEN,    &xTrue,     sizeof( CK_BBOOL )        },
        { CKA_SIGN,     &xTrue,     sizeof( CK_BBOOL )        },
        { CKA_VERIFY,   &xTrue,     sizeof( CK_BBOOL )        },
        { CKA_VALUE,    pxKeyValue, sizeof( pxKeyValue ) - 1  }
    };

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        PKCS11_PAL_SaveObject_IgnoreAndReturn( 1 );
        mock_osal_mutex_lock_IgnoreAndReturn( 0 );
        mock_osal_mutex_unlock_IgnoreAndReturn( 0 );
        xResult = C_CreateObject( xSession,
                                  ( CK_ATTRIBUTE_PTR ) &xSHA256HMACTemplate,
                                  sizeof( xSHA256HMACTemplate ) / sizeof( CK_ATTRIBUTE ),
                                  &xObject );

        TEST_ASSERT_EQUAL( CKR_OK, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}

/*!
 * @brief C_CreateObject Creating a SHA256-HMAC invalid token values.
 *
 */
void test_pkcs11_C_CreateObjectSHA256HMACKeyBadAtts( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = CK_INVALID_HANDLE;
    CK_KEY_TYPE xKeyType = CKK_SHA256_HMAC;
    CK_OBJECT_CLASS xKeyClass = CKO_SECRET_KEY;
    CK_BBOOL xFalse = CK_FALSE;
    CK_OBJECT_HANDLE xObject = CK_INVALID_HANDLE;
    CK_BYTE pcLabel[] = pkcs11configLABEL_HMAC_KEY;

    CK_BYTE pxKeyValue[] = "abcdabcdabcdabcdabcdabcdabcdabcd";

    CK_ATTRIBUTE xSHA256HMACTemplate[] =
    {
        { CKA_CLASS,    &xKeyClass, sizeof( CK_OBJECT_CLASS ) },
        { CKA_KEY_TYPE, &xKeyType,  sizeof( CK_KEY_TYPE )     },
        { CKA_LABEL,    pcLabel,    sizeof( pcLabel ) - 1     },
        { CKA_TOKEN,    &xFalse,    sizeof( CK_BBOOL )        },
        { CKA_SIGN,     &xFalse,    sizeof( CK_BBOOL )        },
        { CKA_VERIFY,   &xFalse,    sizeof( CK_BBOOL )        },
        { CKA_VALUE,    pxKeyValue, sizeof( pxKeyValue ) - 1  }
    };

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        xResult = C_CreateObject( xSession,
                                  ( CK_ATTRIBUTE_PTR ) &xSHA256HMACTemplate,
                                  sizeof( xSHA256HMACTemplate ) / sizeof( CK_ATTRIBUTE ),
                                  &xObject );

        TEST_ASSERT_EQUAL( CKR_ATTRIBUTE_VALUE_INVALID, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}

/*!
 * @brief C_CreateObject Creating a SHA256-HMAC unknown attribute.
 *
 */
void test_pkcs11_C_CreateObjectSHA256HMACKeyUnknownAtt( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = CK_INVALID_HANDLE;
    CK_KEY_TYPE xKeyType = CKK_SHA256_HMAC;
    CK_OBJECT_CLASS xKeyClass = CKO_SECRET_KEY;
    CK_BBOOL xTrue = CK_TRUE;
    CK_OBJECT_HANDLE xObject = CK_INVALID_HANDLE;
    CK_BYTE pcLabel[] = pkcs11configLABEL_HMAC_KEY;

    CK_BYTE pxKeyValue[] = "abcdabcdabcdabcdabcdabcdabcdabcd";

    CK_ATTRIBUTE xSHA256HMACTemplate[] =
    {
        { CKA_CLASS,    &xKeyClass, sizeof( CK_OBJECT_CLASS ) },
        { CKA_KEY_TYPE, &xKeyType,  sizeof( CK_KEY_TYPE )     },
        { CKA_LABEL,    pcLabel,    sizeof( pcLabel ) - 1     },
        { CKA_SUBJECT,  &xTrue,     sizeof( CK_BBOOL )        },
        { CKA_SIGN,     &xTrue,     sizeof( CK_BBOOL )        },
        { CKA_VERIFY,   &xTrue,     sizeof( CK_BBOOL )        },
        { CKA_VALUE,    pxKeyValue, sizeof( pxKeyValue ) - 1  }
    };

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        xResult = C_CreateObject( xSession,
                                  ( CK_ATTRIBUTE_PTR ) &xSHA256HMACTemplate,
                                  sizeof( xSHA256HMACTemplate ) / sizeof( CK_ATTRIBUTE ),
                                  &xObject );

        TEST_ASSERT_EQUAL( CKR_ATTRIBUTE_TYPE_INVALID, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}

/*!
 * @brief C_CreateObject Creating a SHA256-HMAC missing label.
 *
 */
void test_pkcs11_C_CreateObjectSHA256HMACKeyMissingLabel( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = CK_INVALID_HANDLE;
    CK_KEY_TYPE xKeyType = CKK_SHA256_HMAC;
    CK_OBJECT_CLASS xKeyClass = CKO_SECRET_KEY;
    CK_BBOOL xTrue = CK_TRUE;
    CK_OBJECT_HANDLE xObject = CK_INVALID_HANDLE;
    CK_BYTE pcLabel[] = pkcs11configLABEL_HMAC_KEY;

    CK_BYTE pxKeyValue[] = "abcdabcdabcdabcdabcdabcdabcdabcd";

    CK_ATTRIBUTE xSHA256HMACTemplate[] =
    {
        { CKA_CLASS,    &xKeyClass, sizeof( CK_OBJECT_CLASS ) },
        { CKA_KEY_TYPE, &xKeyType,  sizeof( CK_KEY_TYPE )     },
        { CKA_TOKEN,    &xTrue,     sizeof( CK_BBOOL )        },
        { CKA_SIGN,     &xTrue,     sizeof( CK_BBOOL )        },
        { CKA_VERIFY,   &xTrue,     sizeof( CK_BBOOL )        },
        { CKA_VALUE,    pxKeyValue, sizeof( pxKeyValue ) - 1  }
    };

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        xResult = C_CreateObject( xSession,
                                  ( CK_ATTRIBUTE_PTR ) &xSHA256HMACTemplate,
                                  sizeof( xSHA256HMACTemplate ) / sizeof( CK_ATTRIBUTE ),
                                  &xObject );

        TEST_ASSERT_EQUAL( CKR_ARGUMENTS_BAD, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}

/*!
 * @brief C_CreateObject Creating a SHA256-HMAC NULL secret key.
 *
 */
void test_pkcs11_C_CreateObjectSHA256HMACKeyNullSecretKey( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = CK_INVALID_HANDLE;
    CK_KEY_TYPE xKeyType = CKK_SHA256_HMAC;
    CK_OBJECT_CLASS xKeyClass = CKO_SECRET_KEY;
    CK_BBOOL xTrue = CK_TRUE;
    CK_OBJECT_HANDLE xObject = CK_INVALID_HANDLE;
    CK_BYTE pcLabel[] = pkcs11configLABEL_HMAC_KEY;

    CK_ATTRIBUTE xSHA256HMACTemplate[] =
    {
        { CKA_CLASS,    &xKeyClass, sizeof( CK_OBJECT_CLASS ) },
        { CKA_KEY_TYPE, &xKeyType,  sizeof( CK_KEY_TYPE )     },
        { CKA_LABEL,    pcLabel,    sizeof( pcLabel ) - 1     },
        { CKA_TOKEN,    &xTrue,     sizeof( CK_BBOOL )        },
        { CKA_SIGN,     &xTrue,     sizeof( CK_BBOOL )        },
        { CKA_VERIFY,   &xTrue,     sizeof( CK_BBOOL )        },
        { CKA_VALUE,    NULL,       0                         }
    };

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        PKCS11_PAL_SaveObject_IgnoreAndReturn( 0 );
        xResult = C_CreateObject( xSession,
                                  ( CK_ATTRIBUTE_PTR ) &xSHA256HMACTemplate,
                                  sizeof( xSHA256HMACTemplate ) / sizeof( CK_ATTRIBUTE ),
                                  &xObject );

        TEST_ASSERT_EQUAL( CKR_ATTRIBUTE_VALUE_INVALID, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}

/*!
 * @brief C_CreateObject Creating a SHA256-HMAC short secret key.
 *
 */
void test_pkcs11_C_CreateObjectSHA256HMACKeyShortSecretKey( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = CK_INVALID_HANDLE;
    CK_KEY_TYPE xKeyType = CKK_SHA256_HMAC;
    CK_OBJECT_CLASS xKeyClass = CKO_SECRET_KEY;
    CK_BBOOL xTrue = CK_TRUE;
    CK_OBJECT_HANDLE xObject = CK_INVALID_HANDLE;
    CK_BYTE pcLabel[] = pkcs11configLABEL_HMAC_KEY;

    CK_BYTE pxKeyValue[] = "abcdabcdabcdabcd";

    CK_ATTRIBUTE xSHA256HMACTemplate[] =
    {
        { CKA_CLASS,    &xKeyClass, sizeof( CK_OBJECT_CLASS ) },
        { CKA_KEY_TYPE, &xKeyType,  sizeof( CK_KEY_TYPE )     },
        { CKA_LABEL,    pcLabel,    sizeof( pcLabel ) - 1     },
        { CKA_TOKEN,    &xTrue,     sizeof( CK_BBOOL )        },
        { CKA_SIGN,     &xTrue,     sizeof( CK_BBOOL )        },
        { CKA_VERIFY,   &xTrue,     sizeof( CK_BBOOL )        },
        { CKA_VALUE,    pxKeyValue, sizeof( pxKeyValue ) - 1  }
    };

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        PKCS11_PAL_SaveObject_IgnoreAndReturn( 0 );
        xResult = C_CreateObject( xSession,
                                  ( CK_ATTRIBUTE_PTR ) &xSHA256HMACTemplate,
                                  sizeof( xSHA256HMACTemplate ) / sizeof( CK_ATTRIBUTE ),
                                  &xObject );

        TEST_ASSERT_EQUAL( CKR_ATTRIBUTE_VALUE_INVALID, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}

/*!
 * @brief C_CreateObject Creating a SHA256-HMAC secret key fails to write to PKCS #11 PAL.
 *
 */
void test_pkcs11_C_CreateObjectSHA256HMACKeyPalFailure( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = CK_INVALID_HANDLE;
    CK_KEY_TYPE xKeyType = CKK_SHA256_HMAC;
    CK_OBJECT_CLASS xKeyClass = CKO_SECRET_KEY;
    CK_BBOOL xTrue = CK_TRUE;
    CK_OBJECT_HANDLE xObject = CK_INVALID_HANDLE;
    CK_BYTE pcLabel[] = pkcs11configLABEL_HMAC_KEY;

    CK_BYTE pxKeyValue[] = "abcdabcdabcdabcdabcdabcdabcdabcd";

    CK_ATTRIBUTE xSHA256HMACTemplate[] =
    {
        { CKA_CLASS,    &xKeyClass, sizeof( CK_OBJECT_CLASS ) },
        { CKA_KEY_TYPE, &xKeyType,  sizeof( CK_KEY_TYPE )     },
        { CKA_LABEL,    pcLabel,    sizeof( pcLabel ) - 1     },
        { CKA_TOKEN,    &xTrue,     sizeof( CK_BBOOL )        },
        { CKA_SIGN,     &xTrue,     sizeof( CK_BBOOL )        },
        { CKA_VERIFY,   &xTrue,     sizeof( CK_BBOOL )        },
        { CKA_VALUE,    pxKeyValue, sizeof( pxKeyValue ) - 1  }
    };

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        PKCS11_PAL_SaveObject_IgnoreAndReturn( 0 );
        xResult = C_CreateObject( xSession,
                                  ( CK_ATTRIBUTE_PTR ) &xSHA256HMACTemplate,
                                  sizeof( xSHA256HMACTemplate ) / sizeof( CK_ATTRIBUTE ),
                                  &xObject );

        TEST_ASSERT_EQUAL( CKR_DEVICE_MEMORY, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}

/*!
 * @brief C_CreateObject Creating a SHA256-HMAC invalid HMAC key type.
 *
 */
void test_pkcs11_C_CreateObjectSHA256HMACKeyInvalidKeyType( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = CK_INVALID_HANDLE;
    CK_KEY_TYPE xKeyType = CKK_MD5_HMAC;
    CK_OBJECT_CLASS xKeyClass = CKO_SECRET_KEY;
    CK_BBOOL xTrue = CK_TRUE;
    CK_OBJECT_HANDLE xObject = CK_INVALID_HANDLE;
    CK_BYTE pcLabel[] = pkcs11configLABEL_HMAC_KEY;

    CK_BYTE pxKeyValue[] = "abcdabcdabcdabcdabcdabcdabcdabcd";

    CK_ATTRIBUTE xSHA256HMACTemplate[] =
    {
        { CKA_CLASS,    &xKeyClass, sizeof( CK_OBJECT_CLASS ) },
        { CKA_KEY_TYPE, &xKeyType,  sizeof( CK_KEY_TYPE )     },
        { CKA_LABEL,    pcLabel,    sizeof( pcLabel ) - 1     },
        { CKA_TOKEN,    &xTrue,     sizeof( CK_BBOOL )        },
        { CKA_SIGN,     &xTrue,     sizeof( CK_BBOOL )        },
        { CKA_VERIFY,   &xTrue,     sizeof( CK_BBOOL )        },
        { CKA_VALUE,    pxKeyValue, sizeof( pxKeyValue ) - 1  }
    };

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        PKCS11_PAL_SaveObject_IgnoreAndReturn( 1 );
        mock_osal_mutex_lock_IgnoreAndReturn( 0 );
        mock_osal_mutex_unlock_IgnoreAndReturn( 0 );
        xResult = C_CreateObject( xSession,
                                  ( CK_ATTRIBUTE_PTR ) &xSHA256HMACTemplate,
                                  sizeof( xSHA256HMACTemplate ) / sizeof( CK_ATTRIBUTE ),
                                  &xObject );

        TEST_ASSERT_EQUAL( CKR_MECHANISM_INVALID, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}

/*!
 * @brief C_CreateObject Creating a AES-CMAC secret key happy path.
 *
 */
void test_pkcs11_C_CreateObjectAESCMACKey( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = CK_INVALID_HANDLE;
    CK_KEY_TYPE xKeyType = CKK_AES;
    CK_OBJECT_CLASS xKeyClass = CKO_SECRET_KEY;
    CK_BBOOL xTrue = CK_TRUE;
    CK_OBJECT_HANDLE xObject = CK_INVALID_HANDLE;
    CK_BYTE pcLabel[] = pkcs11configLABEL_CMAC_KEY;

    CK_BYTE pxKeyValue[] = "abcdabcdabcdabcdabcdabcdabcdabcd";

    CK_ATTRIBUTE xAESCMACTemplate[] =
    {
        { CKA_CLASS,    &xKeyClass, sizeof( CK_OBJECT_CLASS ) },
        { CKA_KEY_TYPE, &xKeyType,  sizeof( CK_KEY_TYPE )     },
        { CKA_LABEL,    pcLabel,    sizeof( pcLabel ) - 1     },
        { CKA_TOKEN,    &xTrue,     sizeof( CK_BBOOL )        },
        { CKA_SIGN,     &xTrue,     sizeof( CK_BBOOL )        },
        { CKA_VERIFY,   &xTrue,     sizeof( CK_BBOOL )        },
        { CKA_VALUE,    pxKeyValue, sizeof( pxKeyValue ) - 1  }
    };

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        PKCS11_PAL_SaveObject_IgnoreAndReturn( 1 );
        mock_osal_mutex_lock_IgnoreAndReturn( 0 );
        mock_osal_mutex_unlock_IgnoreAndReturn( 0 );
        xResult = C_CreateObject( xSession,
                                  ( CK_ATTRIBUTE_PTR ) &xAESCMACTemplate,
                                  sizeof( xAESCMACTemplate ) / sizeof( CK_ATTRIBUTE ),
                                  &xObject );

        TEST_ASSERT_EQUAL( CKR_OK, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}

/*!
 * @brief C_CreateObject Creating a AES-CMAC invalid token values.
 *
 */
void test_pkcs11_C_CreateObjectAESCMACKeyBadAtts( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = CK_INVALID_HANDLE;
    CK_KEY_TYPE xKeyType = CKK_AES;
    CK_OBJECT_CLASS xKeyClass = CKO_SECRET_KEY;
    CK_BBOOL xFalse = CK_FALSE;
    CK_OBJECT_HANDLE xObject = CK_INVALID_HANDLE;
    CK_BYTE pcLabel[] = pkcs11configLABEL_CMAC_KEY;

    CK_BYTE pxKeyValue[] = "abcdabcdabcdabcdabcdabcdabcdabcd";

    CK_ATTRIBUTE xAESCMACTemplate[] =
    {
        { CKA_CLASS,    &xKeyClass, sizeof( CK_OBJECT_CLASS ) },
        { CKA_KEY_TYPE, &xKeyType,  sizeof( CK_KEY_TYPE )     },
        { CKA_LABEL,    pcLabel,    sizeof( pcLabel ) - 1     },
        { CKA_TOKEN,    &xFalse,    sizeof( CK_BBOOL )        },
        { CKA_SIGN,     &xFalse,    sizeof( CK_BBOOL )        },
        { CKA_VERIFY,   &xFalse,    sizeof( CK_BBOOL )        },
        { CKA_VALUE,    pxKeyValue, sizeof( pxKeyValue ) - 1  }
    };

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        xResult = C_CreateObject( xSession,
                                  ( CK_ATTRIBUTE_PTR ) &xAESCMACTemplate,
                                  sizeof( xAESCMACTemplate ) / sizeof( CK_ATTRIBUTE ),
                                  &xObject );

        TEST_ASSERT_EQUAL( CKR_ATTRIBUTE_VALUE_INVALID, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}

/*!
 * @brief C_CreateObject Creating a AES-CMAC unknown attribute.
 *
 */
void test_pkcs11_C_CreateObjectAESCMACKeyUnknownAtt( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = CK_INVALID_HANDLE;
    CK_KEY_TYPE xKeyType = CKK_AES;
    CK_OBJECT_CLASS xKeyClass = CKO_SECRET_KEY;
    CK_BBOOL xTrue = CK_TRUE;
    CK_OBJECT_HANDLE xObject = CK_INVALID_HANDLE;
    CK_BYTE pcLabel[] = pkcs11configLABEL_CMAC_KEY;

    CK_BYTE pxKeyValue[] = "abcdabcdabcdabcdabcdabcdabcdabcd";

    CK_ATTRIBUTE xAESCMACTemplate[] =
    {
        { CKA_CLASS,    &xKeyClass, sizeof( CK_OBJECT_CLASS ) },
        { CKA_KEY_TYPE, &xKeyType,  sizeof( CK_KEY_TYPE )     },
        { CKA_LABEL,    pcLabel,    sizeof( pcLabel ) - 1     },
        { CKA_SUBJECT,  &xTrue,     sizeof( CK_BBOOL )        },
        { CKA_SIGN,     &xTrue,     sizeof( CK_BBOOL )        },
        { CKA_VERIFY,   &xTrue,     sizeof( CK_BBOOL )        },
        { CKA_VALUE,    pxKeyValue, sizeof( pxKeyValue ) - 1  }
    };

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        xResult = C_CreateObject( xSession,
                                  ( CK_ATTRIBUTE_PTR ) &xAESCMACTemplate,
                                  sizeof( xAESCMACTemplate ) / sizeof( CK_ATTRIBUTE ),
                                  &xObject );

        TEST_ASSERT_EQUAL( CKR_ATTRIBUTE_TYPE_INVALID, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}

/*!
 * @brief C_CreateObject Creating a AES-CMAC missing label.
 *
 */
void test_pkcs11_C_CreateObjectAESCMACKeyMissingLabel( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = CK_INVALID_HANDLE;
    CK_KEY_TYPE xKeyType = CKK_AES;
    CK_OBJECT_CLASS xKeyClass = CKO_SECRET_KEY;
    CK_BBOOL xTrue = CK_TRUE;
    CK_OBJECT_HANDLE xObject = CK_INVALID_HANDLE;
    CK_BYTE pcLabel[] = pkcs11configLABEL_CMAC_KEY;

    CK_BYTE pxKeyValue[] = "abcdabcdabcdabcdabcdabcdabcdabcd";

    CK_ATTRIBUTE xAESCMACTemplate[] =
    {
        { CKA_CLASS,    &xKeyClass, sizeof( CK_OBJECT_CLASS ) },
        { CKA_KEY_TYPE, &xKeyType,  sizeof( CK_KEY_TYPE )     },
        { CKA_TOKEN,    &xTrue,     sizeof( CK_BBOOL )        },
        { CKA_SIGN,     &xTrue,     sizeof( CK_BBOOL )        },
        { CKA_VERIFY,   &xTrue,     sizeof( CK_BBOOL )        },
        { CKA_VALUE,    pxKeyValue, sizeof( pxKeyValue ) - 1  }
    };

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        xResult = C_CreateObject( xSession,
                                  ( CK_ATTRIBUTE_PTR ) &xAESCMACTemplate,
                                  sizeof( xAESCMACTemplate ) / sizeof( CK_ATTRIBUTE ),
                                  &xObject );

        TEST_ASSERT_EQUAL( CKR_ARGUMENTS_BAD, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}

/*!
 * @brief C_CreateObject Creating a AES-CMAC NULL secret key.
 *
 */
void test_pkcs11_C_CreateObjectAESCMACKeyNullSecretKey( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = CK_INVALID_HANDLE;
    CK_KEY_TYPE xKeyType = CKK_AES;
    CK_OBJECT_CLASS xKeyClass = CKO_SECRET_KEY;
    CK_BBOOL xTrue = CK_TRUE;
    CK_OBJECT_HANDLE xObject = CK_INVALID_HANDLE;
    CK_BYTE pcLabel[] = pkcs11configLABEL_CMAC_KEY;

    CK_ATTRIBUTE xAESCMACTemplate[] =
    {
        { CKA_CLASS,    &xKeyClass, sizeof( CK_OBJECT_CLASS ) },
        { CKA_KEY_TYPE, &xKeyType,  sizeof( CK_KEY_TYPE )     },
        { CKA_LABEL,    pcLabel,    sizeof( pcLabel ) - 1     },
        { CKA_TOKEN,    &xTrue,     sizeof( CK_BBOOL )        },
        { CKA_SIGN,     &xTrue,     sizeof( CK_BBOOL )        },
        { CKA_VERIFY,   &xTrue,     sizeof( CK_BBOOL )        },
        { CKA_VALUE,    NULL,       0                         }
    };

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        PKCS11_PAL_SaveObject_IgnoreAndReturn( 0 );
        xResult = C_CreateObject( xSession,
                                  ( CK_ATTRIBUTE_PTR ) &xAESCMACTemplate,
                                  sizeof( xAESCMACTemplate ) / sizeof( CK_ATTRIBUTE ),
                                  &xObject );

        TEST_ASSERT_EQUAL( CKR_ATTRIBUTE_VALUE_INVALID, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}

/*!
 * @brief C_CreateObject Creating a AES-CMAC short secret key.
 *
 */
void test_pkcs11_C_CreateObjectAESCMACKeyShortSecretKey( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = CK_INVALID_HANDLE;
    CK_KEY_TYPE xKeyType = CKK_AES;
    CK_OBJECT_CLASS xKeyClass = CKO_SECRET_KEY;
    CK_BBOOL xTrue = CK_TRUE;
    CK_OBJECT_HANDLE xObject = CK_INVALID_HANDLE;
    CK_BYTE pcLabel[] = pkcs11configLABEL_CMAC_KEY;

    CK_BYTE pxKeyValue[] = "abcdabcdabcdab";

    CK_ATTRIBUTE xAESCMACTemplate[] =
    {
        { CKA_CLASS,    &xKeyClass, sizeof( CK_OBJECT_CLASS ) },
        { CKA_KEY_TYPE, &xKeyType,  sizeof( CK_KEY_TYPE )     },
        { CKA_LABEL,    pcLabel,    sizeof( pcLabel ) - 1     },
        { CKA_TOKEN,    &xTrue,     sizeof( CK_BBOOL )        },
        { CKA_SIGN,     &xTrue,     sizeof( CK_BBOOL )        },
        { CKA_VERIFY,   &xTrue,     sizeof( CK_BBOOL )        },
        { CKA_VALUE,    pxKeyValue, sizeof( pxKeyValue ) - 1  }
    };

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        PKCS11_PAL_SaveObject_IgnoreAndReturn( 0 );
        xResult = C_CreateObject( xSession,
                                  ( CK_ATTRIBUTE_PTR ) &xAESCMACTemplate,
                                  sizeof( xAESCMACTemplate ) / sizeof( CK_ATTRIBUTE ),
                                  &xObject );

        TEST_ASSERT_EQUAL( CKR_ATTRIBUTE_VALUE_INVALID, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}

/*!
 * @brief C_CreateObject Creating a AES-ChAC secret key fails to write to PKCS #11 PAL.
 *
 */
void test_pkcs11_C_CreateObjectAESCMACKeyPalFailure( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = CK_INVALID_HANDLE;
    CK_KEY_TYPE xKeyType = CKK_AES;
    CK_OBJECT_CLASS xKeyClass = CKO_SECRET_KEY;
    CK_BBOOL xTrue = CK_TRUE;
    CK_OBJECT_HANDLE xObject = CK_INVALID_HANDLE;
    CK_BYTE pcLabel[] = pkcs11configLABEL_CMAC_KEY;

    CK_BYTE pxKeyValue[] = "abcdabcdabcdabcdabcdabcdabcdabcd";

    CK_ATTRIBUTE xAESCMACTemplate[] =
    {
        { CKA_CLASS,    &xKeyClass, sizeof( CK_OBJECT_CLASS ) },
        { CKA_KEY_TYPE, &xKeyType,  sizeof( CK_KEY_TYPE )     },
        { CKA_LABEL,    pcLabel,    sizeof( pcLabel ) - 1     },
        { CKA_TOKEN,    &xTrue,     sizeof( CK_BBOOL )        },
        { CKA_SIGN,     &xTrue,     sizeof( CK_BBOOL )        },
        { CKA_VERIFY,   &xTrue,     sizeof( CK_BBOOL )        },
        { CKA_VALUE,    pxKeyValue, sizeof( pxKeyValue ) - 1  }
    };

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        PKCS11_PAL_SaveObject_IgnoreAndReturn( 0 );
        xResult = C_CreateObject( xSession,
                                  ( CK_ATTRIBUTE_PTR ) &xAESCMACTemplate,
                                  sizeof( xAESCMACTemplate ) / sizeof( CK_ATTRIBUTE ),
                                  &xObject );

        TEST_ASSERT_EQUAL( CKR_DEVICE_MEMORY, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}

/*!
 * @brief C_CreateObject Creating a AES-CMAC invalid CMAC key type.
 *
 */
void test_pkcs11_C_CreateObjectAESCMACKeyInvalidKeyType( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = CK_INVALID_HANDLE;
    CK_KEY_TYPE xKeyType = CKK_MD5_HMAC;
    CK_OBJECT_CLASS xKeyClass = CKO_SECRET_KEY;
    CK_BBOOL xTrue = CK_TRUE;
    CK_OBJECT_HANDLE xObject = CK_INVALID_HANDLE;
    CK_BYTE pcLabel[] = pkcs11configLABEL_CMAC_KEY;

    CK_BYTE pxKeyValue[] = "abcdabcdabcdabcdabcdabcdabcdabcd";

    CK_ATTRIBUTE xAESCMACTemplate[] =
    {
        { CKA_CLASS,    &xKeyClass, sizeof( CK_OBJECT_CLASS ) },
        { CKA_KEY_TYPE, &xKeyType,  sizeof( CK_KEY_TYPE )     },
        { CKA_LABEL,    pcLabel,    sizeof( pcLabel ) - 1     },
        { CKA_TOKEN,    &xTrue,     sizeof( CK_BBOOL )        },
        { CKA_SIGN,     &xTrue,     sizeof( CK_BBOOL )        },
        { CKA_VERIFY,   &xTrue,     sizeof( CK_BBOOL )        },
        { CKA_VALUE,    pxKeyValue, sizeof( pxKeyValue ) - 1  }
    };

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        PKCS11_PAL_SaveObject_IgnoreAndReturn( 1 );
        mock_osal_mutex_lock_IgnoreAndReturn( 0 );
        mock_osal_mutex_unlock_IgnoreAndReturn( 0 );
        xResult = C_CreateObject( xSession,
                                  ( CK_ATTRIBUTE_PTR ) &xAESCMACTemplate,
                                  sizeof( xAESCMACTemplate ) / sizeof( CK_ATTRIBUTE ),
                                  &xObject );

        TEST_ASSERT_EQUAL( CKR_MECHANISM_INVALID, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}

/* ======================  TESTING C_GetAttributeValue  ============================ */

/*!
 * @brief C_GetAttributeValue get value of a certificate happy path.
 *
 */
void test_pkcs11_C_GetAttributeValueCert( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = 0;
    CK_OBJECT_HANDLE xObject = 0;
    CK_ULONG ulCount = 1;
    PKCS11_CertificateTemplate_t xCertificateTemplate = { 0 };

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        xResult = prvCreateCert( &xSession, &xObject );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        /* Get Certificate value. */
        PKCS11_PAL_GetObjectValue_IgnoreAndReturn( CKR_OK );
        mbedtls_pk_init_CMockIgnore();
        mbedtls_x509_crt_init_CMockIgnore();
        mbedtls_pk_parse_key_IgnoreAndReturn( 1 );
        mbedtls_pk_parse_public_key_IgnoreAndReturn( 1 );
        mbedtls_x509_crt_parse_IgnoreAndReturn( 0 );
        PKCS11_PAL_GetObjectValueCleanup_CMockIgnore();
        mbedtls_pk_free_CMockIgnore();
        mbedtls_x509_crt_free_CMockIgnore();
        xResult = C_GetAttributeValue( xSession, xObject, ( CK_ATTRIBUTE_PTR ) &xCertificateTemplate, ulCount );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}

/*!
 * @brief C_GetAttributeValue test attribute parsing of PKCS #11 templates.
 *
 */
void test_pkcs11_C_GetAttributeValueAttParsing( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = 0;
    CK_OBJECT_HANDLE xObject = 0;
    CK_OBJECT_HANDLE xObjectPub = 0;
    CK_ULONG ulCount = 1;
    CK_ULONG ulLength = 1;
    CK_BYTE pulKnownBuf[] = pkcs11DER_ENCODED_OID_P256;
    CK_BYTE pulBuf[ sizeof( pulKnownBuf ) ] = { 0 };
    CK_BYTE ulPoint[ pkcs11EC_POINT_LENGTH ] = { 0 };
    CK_BYTE ulKnownPoint = 0x04;
    CK_BBOOL xIsPrivate = CK_FALSE;
    CK_OBJECT_CLASS xPrivateKeyClass = { 0 };
    CK_OBJECT_CLASS xKnownPrivateKeyClass = CKO_PRIVATE_KEY;
    CK_ATTRIBUTE xTemplate = { CKA_EC_PARAMS, pulBuf, sizeof( pulBuf ) };

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        xResult = prvCreateEcPriv( &xSession, &xObject );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        xResult = prvCreateEcPub( &xSession, &xObjectPub );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );


        /* EC Params Case */
        mbedtls_pk_init_CMockIgnore();
        mbedtls_x509_crt_init_CMockIgnore();
        mbedtls_pk_parse_key_IgnoreAndReturn( 0 );
        PKCS11_PAL_GetObjectValueCleanup_CMockIgnore();
        mbedtls_pk_free_CMockIgnore();
        mbedtls_x509_crt_free_CMockIgnore();
        xResult = C_GetAttributeValue( xSession, xObject, ( CK_ATTRIBUTE_PTR ) &xTemplate, ulCount );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );
        TEST_ASSERT_EQUAL_MEMORY( pulKnownBuf, xTemplate.pValue, sizeof( pulKnownBuf ) );

        /* EC Point Case */
        mbedtls_ecp_tls_write_point_IgnoreAndReturn( 1 );
        xTemplate.type = CKA_EC_POINT;
        xTemplate.pValue = NULL;
        xTemplate.ulValueLen = 0;

        xResult = C_GetAttributeValue( xSession, xObject, ( CK_ATTRIBUTE_PTR ) &xTemplate, ulCount );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        TEST_ASSERT_EQUAL( pkcs11EC_POINT_LENGTH, xTemplate.ulValueLen );

        xTemplate.pValue = &ulPoint;
        xTemplate.ulValueLen = sizeof( ulPoint );

        xResult = C_GetAttributeValue( xSession, xObject, ( CK_ATTRIBUTE_PTR ) &xTemplate, ulCount );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );
        TEST_ASSERT_EQUAL( ulKnownPoint, ulPoint[ 0 ] );

        xTemplate.pValue = &ulPoint;
        xTemplate.ulValueLen = sizeof( ulPoint );

        mbedtls_ecp_tls_write_point_IgnoreAndReturn( MBEDTLS_ERR_ECP_BUFFER_TOO_SMALL );
        xResult = C_GetAttributeValue( xSession, xObject, ( CK_ATTRIBUTE_PTR ) &xTemplate, ulCount );
        TEST_ASSERT_EQUAL( CKR_BUFFER_TOO_SMALL, xResult );

        mbedtls_ecp_tls_write_point_IgnoreAndReturn( -1 );
        xTemplate.pValue = &ulPoint;
        xTemplate.ulValueLen = sizeof( ulPoint );

        xResult = C_GetAttributeValue( xSession, xObject, ( CK_ATTRIBUTE_PTR ) &xTemplate, ulCount );
        TEST_ASSERT_EQUAL( CKR_FUNCTION_FAILED, xResult );

        mbedtls_ecp_tls_write_point_IgnoreAndReturn( 1 );

        /* Unknown attribute. */
        xTemplate.type = CKA_MODULUS;

        xResult = C_GetAttributeValue( xSession, xObject, ( CK_ATTRIBUTE_PTR ) &xTemplate, ulCount );
        TEST_ASSERT_EQUAL( CKR_ATTRIBUTE_TYPE_INVALID, xResult );

        /* CKA Class Case */
        xTemplate.type = CKA_CLASS;
        xTemplate.pValue = NULL;
        xTemplate.ulValueLen = 0;

        mbedtls_pk_parse_key_IgnoreAndReturn( 0 );
        xResult = C_GetAttributeValue( xSession, xObject, ( CK_ATTRIBUTE_PTR ) &xTemplate, ulCount );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );
        TEST_ASSERT_EQUAL( NULL, xTemplate.pValue );
        TEST_ASSERT_EQUAL( sizeof( xPrivateKeyClass ), xTemplate.ulValueLen );

        xTemplate.pValue = &xPrivateKeyClass;

        xResult = C_GetAttributeValue( xSession, xObject, ( CK_ATTRIBUTE_PTR ) &xTemplate, ulCount );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );
        TEST_ASSERT_EQUAL( sizeof( xPrivateKeyClass ), xTemplate.ulValueLen );
        TEST_ASSERT_EQUAL_MEMORY( &xKnownPrivateKeyClass, xTemplate.pValue, sizeof( xPrivateKeyClass ) );

        /* CKA Value Case */
        xTemplate.type = CKA_VALUE;
        xTemplate.pValue = NULL;
        xTemplate.ulValueLen = 0;

        PKCS11_PAL_GetObjectValue_ExpectAnyArgsAndReturn( CKR_OK );
        PKCS11_PAL_GetObjectValue_ReturnThruPtr_pIsPrivate( &xIsPrivate );
        PKCS11_PAL_GetObjectValue_ReturnThruPtr_pulDataSize( &ulLength );
        mbedtls_pk_parse_key_IgnoreAndReturn( 1 );
        mbedtls_pk_parse_public_key_ExpectAnyArgsAndReturn( 0 );
        xResult = C_GetAttributeValue( xSession, xObjectPub, ( CK_ATTRIBUTE_PTR ) &xTemplate, ulCount );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );
        TEST_ASSERT_EQUAL( 1, xTemplate.ulValueLen );

        xTemplate.type = CKA_VALUE;
        xTemplate.pValue = &ulPoint;
        xTemplate.ulValueLen = 0;

        PKCS11_PAL_GetObjectValue_ExpectAnyArgsAndReturn( CKR_OK );
        PKCS11_PAL_GetObjectValue_ReturnThruPtr_pIsPrivate( &xIsPrivate );
        PKCS11_PAL_GetObjectValue_ReturnThruPtr_pulDataSize( &ulLength );
        mbedtls_pk_parse_key_IgnoreAndReturn( 0 );
        xResult = C_GetAttributeValue( xSession, xObjectPub, ( CK_ATTRIBUTE_PTR ) &xTemplate, ulCount );
        TEST_ASSERT_EQUAL( CKR_BUFFER_TOO_SMALL, xResult );
        TEST_ASSERT_EQUAL( 0, xTemplate.ulValueLen );

        xTemplate.type = CKA_VALUE;
        xTemplate.pValue = &ulLength;
        xTemplate.ulValueLen = 1;

        PKCS11_PAL_GetObjectValue_ExpectAnyArgsAndReturn( CKR_OK );
        PKCS11_PAL_GetObjectValue_ReturnThruPtr_pIsPrivate( &xIsPrivate );
        xResult = C_GetAttributeValue( xSession, xObjectPub, ( CK_ATTRIBUTE_PTR ) &xTemplate, ulCount );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );
        TEST_ASSERT_EQUAL( 1, xTemplate.ulValueLen );
        TEST_ASSERT_EQUAL( 1, *( uint32_t * ) xTemplate.pValue );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}

/*!
 * @brief C_GetAttributeValue paths.
 *
 */
void test_pkcs11_C_GetAttributeValuePrivKey( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = 0;
    CK_OBJECT_HANDLE xObject = 0;
    CK_ULONG ulCount = 1;
    CK_ATTRIBUTE xTemplate = { CKA_VALUE, NULL, 0 };
    CK_KEY_TYPE xKeyType = { 0 };
    CK_KEY_TYPE xKnownKeyType = CKK_EC;

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        xResult = prvCreateEcPriv( &xSession, &xObject );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        PKCS11_PAL_GetObjectValue_IgnoreAndReturn( CKR_OK );
        mbedtls_pk_init_CMockIgnore();
        mbedtls_x509_crt_init_CMockIgnore();
        mbedtls_pk_parse_key_IgnoreAndReturn( 0 );
        PKCS11_PAL_GetObjectValueCleanup_CMockIgnore();
        mbedtls_pk_free_CMockIgnore();
        mbedtls_x509_crt_free_CMockIgnore();
        xResult = C_GetAttributeValue( xSession, xObject, ( CK_ATTRIBUTE_PTR ) &xTemplate, ulCount );
        TEST_ASSERT_EQUAL( CKR_ATTRIBUTE_SENSITIVE, xResult );
        TEST_ASSERT_EQUAL( CK_UNAVAILABLE_INFORMATION, xTemplate.ulValueLen );

        xTemplate.type = CKA_KEY_TYPE;
        xTemplate.pValue = NULL;
        xTemplate.ulValueLen = 0;

        xPkType = MBEDTLS_PK_ECKEY;
        xResult = C_GetAttributeValue( xSession, xObject, ( CK_ATTRIBUTE_PTR ) &xTemplate, ulCount );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );
        TEST_ASSERT_EQUAL( sizeof( CK_KEY_TYPE ), xTemplate.ulValueLen );


        xTemplate.type = CKA_KEY_TYPE;
        xTemplate.pValue = &xKeyType;
        xTemplate.ulValueLen = sizeof( CK_KEY_TYPE );

        xResult = C_GetAttributeValue( xSession, xObject, ( CK_ATTRIBUTE_PTR ) &xTemplate, ulCount );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );
        TEST_ASSERT_EQUAL( sizeof( CK_KEY_TYPE ), xTemplate.ulValueLen );
        TEST_ASSERT_EQUAL_MEMORY( &xKnownKeyType, xTemplate.pValue, sizeof( CK_KEY_TYPE ) );

        xTemplate.type = CKA_KEY_TYPE;
        xTemplate.pValue = NULL;
        xTemplate.ulValueLen = 0;

        xResult = C_GetAttributeValue( xSession, xObject, ( CK_ATTRIBUTE_PTR ) &xTemplate, ulCount );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );
        TEST_ASSERT_EQUAL( sizeof( CK_KEY_TYPE ), xTemplate.ulValueLen );


        xTemplate.type = CKA_KEY_TYPE;
        xTemplate.pValue = &xKeyType;
        xTemplate.ulValueLen = sizeof( CK_KEY_TYPE );
        xKnownKeyType = CKK_RSA;

        xPkType = MBEDTLS_PK_RSA;
        xResult = C_GetAttributeValue( xSession, xObject, ( CK_ATTRIBUTE_PTR ) &xTemplate, ulCount );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );
        TEST_ASSERT_EQUAL( sizeof( CK_KEY_TYPE ), xTemplate.ulValueLen );
        TEST_ASSERT_EQUAL_MEMORY( &xKnownKeyType, xTemplate.pValue, sizeof( CK_KEY_TYPE ) );

        xTemplate.type = CKA_KEY_TYPE;
        xTemplate.pValue = NULL;
        xTemplate.ulValueLen = 0;
        xResult = C_GetAttributeValue( xSession, xObject, ( CK_ATTRIBUTE_PTR ) &xTemplate, ulCount );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );
        TEST_ASSERT_EQUAL( sizeof( CK_KEY_TYPE ), xTemplate.ulValueLen );


        xTemplate.type = CKA_KEY_TYPE;
        xTemplate.pValue = &xKeyType;
        xTemplate.ulValueLen = sizeof( CK_KEY_TYPE );
        xKnownKeyType = CKK_ECDSA;

        xPkType = MBEDTLS_PK_ECDSA;
        xResult = C_GetAttributeValue( xSession, xObject, ( CK_ATTRIBUTE_PTR ) &xTemplate, ulCount );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );
        TEST_ASSERT_EQUAL( sizeof( CK_KEY_TYPE ), xTemplate.ulValueLen );
        TEST_ASSERT_EQUAL_MEMORY( &xKnownKeyType, xTemplate.pValue, sizeof( CK_KEY_TYPE ) );


        mbedtls_pk_parse_key_ExpectAnyArgsAndReturn( -1 );
        mbedtls_pk_parse_public_key_ExpectAnyArgsAndReturn( -1 );
        mbedtls_x509_crt_parse_ExpectAnyArgsAndReturn( -1 );
        xResult = C_GetAttributeValue( xSession, xObject, ( CK_ATTRIBUTE_PTR ) &xTemplate, ulCount );
        TEST_ASSERT_EQUAL( CKR_OBJECT_HANDLE_INVALID, xResult );

        xTemplate.type = CKA_CLASS;
        xTemplate.ulValueLen = 0;
        ulCount = 2;
        mbedtls_pk_parse_key_ExpectAnyArgsAndReturn( 0 );
        xResult = C_GetAttributeValue( xSession, xObject, ( CK_ATTRIBUTE_PTR ) &xTemplate, ulCount );
        TEST_ASSERT_EQUAL( CKR_BUFFER_TOO_SMALL, xResult );


        xTemplate.type = CKA_KEY_TYPE;
        mbedtls_pk_parse_key_ExpectAnyArgsAndReturn( 0 );
        xResult = C_GetAttributeValue( xSession, xObject, ( CK_ATTRIBUTE_PTR ) &xTemplate, ulCount );
        TEST_ASSERT_EQUAL( CKR_BUFFER_TOO_SMALL, xResult );


        xTemplate.ulValueLen = sizeof( CKA_KEY_TYPE );
        ulCount = 1;
        mbedtls_pk_parse_key_ExpectAnyArgsAndReturn( 0 );

        xPkType = MBEDTLS_PK_NONE;
        xResult = C_GetAttributeValue( xSession, xObject, ( CK_ATTRIBUTE_PTR ) &xTemplate, ulCount );
        TEST_ASSERT_EQUAL( CKR_ATTRIBUTE_VALUE_INVALID, xResult );

        xTemplate.type = CKA_PRIVATE_EXPONENT;
        mbedtls_pk_parse_key_ExpectAnyArgsAndReturn( 0 );
        xResult = C_GetAttributeValue( xSession, xObject, ( CK_ATTRIBUTE_PTR ) &xTemplate, ulCount );
        TEST_ASSERT_EQUAL( CKR_ATTRIBUTE_SENSITIVE, xResult );


        xTemplate.type = CKA_EC_PARAMS;
        xTemplate.pValue = NULL;
        mbedtls_pk_parse_key_ExpectAnyArgsAndReturn( 0 );
        xResult = C_GetAttributeValue( xSession, xObject, ( CK_ATTRIBUTE_PTR ) &xTemplate, ulCount );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        xTemplate.type = CKA_EC_PARAMS;
        xTemplate.pValue = &ulCount;
        xTemplate.ulValueLen = 1;
        mbedtls_pk_parse_key_ExpectAnyArgsAndReturn( 0 );
        xResult = C_GetAttributeValue( xSession, xObject, ( CK_ATTRIBUTE_PTR ) &xTemplate, ulCount );
        TEST_ASSERT_EQUAL( CKR_BUFFER_TOO_SMALL, xResult );

        xTemplate.type = CKA_EC_POINT;
        xTemplate.pValue = &ulCount;
        xTemplate.ulValueLen = 72;
        mbedtls_pk_parse_key_ExpectAnyArgsAndReturn( 0 );
        xResult = C_GetAttributeValue( xSession, xObject, ( CK_ATTRIBUTE_PTR ) &xTemplate, ulCount );
        TEST_ASSERT_EQUAL( CKR_BUFFER_TOO_SMALL, xResult );

        xTemplate.pValue = &xKeyType;
        xTemplate.ulValueLen = 0;
        mbedtls_pk_parse_key_ExpectAnyArgsAndReturn( 0 );
        xResult = C_GetAttributeValue( xSession, xObject, ( CK_ATTRIBUTE_PTR ) &xTemplate, ulCount );
        TEST_ASSERT_EQUAL( CKR_BUFFER_TOO_SMALL, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}

/*!
 * @brief C_GetAttributeValue bad args.
 *
 */
void test_pkcs11_C_GetAttributeBadArgs( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = 0;
    CK_OBJECT_HANDLE xObject = 0;
    CK_ULONG ulCount = 1;

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        xResult = C_GetAttributeValue( xSession, xObject, NULL, ulCount );
        TEST_ASSERT_EQUAL( CKR_ARGUMENTS_BAD, xResult );

        xResult = C_GetAttributeValue( xSession, xObject, ( CK_ATTRIBUTE_PTR ) &xResult, 0 );
        TEST_ASSERT_EQUAL( CKR_ARGUMENTS_BAD, xResult );

        xResult = C_GetAttributeValue( -1, xObject, ( CK_ATTRIBUTE_PTR ) &xResult, ulCount );
        TEST_ASSERT_EQUAL( CKR_SESSION_HANDLE_INVALID, xResult );

        xResult = C_GetAttributeValue( xSession, 0, ( CK_ATTRIBUTE_PTR ) &xResult, ulCount );
        TEST_ASSERT_EQUAL( CKR_OBJECT_HANDLE_INVALID, xResult );

        xResult = C_GetAttributeValue( xSession, pkcs11configMAX_NUM_OBJECTS + 2, ( CK_ATTRIBUTE_PTR ) &xResult, ulCount );
        TEST_ASSERT_EQUAL( CKR_OBJECT_HANDLE_INVALID, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}

/* ======================  TESTING C_FindObjectsInit  ============================ */

/*!
 * @brief C_FindObjectsInit happy path.
 *
 */
void test_pkcs11_C_FindObjectsInit( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = 0;
    CK_ULONG ulCount = 1;
    CK_OBJECT_HANDLE xObject = 0;
    char * pucLabel = pkcs11configLABEL_DEVICE_CERTIFICATE_FOR_TLS;

    CK_ATTRIBUTE xFindTemplate = { CKA_LABEL, pucLabel, strlen( ( const char * ) pucLabel ) };

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        xResult = prvCreateCert( &xSession, &xObject );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        mbedtls_calloc_Stub( pvPkcs11CallocCb );
        xResult = C_FindObjectsInit( xSession, ( CK_ATTRIBUTE_PTR ) &xFindTemplate, ulCount );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        /* Clean up after C_FindObjectsInit. */
        vPkcs11Free_Stub( vPkcs11FreeCb );
        mbedtls_free_Stub( vPkcs11FreeCb );
        xResult = C_FindObjectsFinal( xSession );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}

/*!
 * @brief C_FindObjectsInit Active Operation.
 *
 */
void test_pkcs11_C_FindObjectsInitActiveOp( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = 0;
    CK_ULONG ulCount = 1;
    CK_OBJECT_HANDLE xObject = 0;
    char * pucLabel = pkcs11configLABEL_DEVICE_CERTIFICATE_FOR_TLS;

    CK_ATTRIBUTE xFindTemplate = { CKA_LABEL, pucLabel, strlen( ( const char * ) pucLabel ) };

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        xResult = prvCreateCert( &xSession, &xObject );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        mbedtls_calloc_Stub( pvPkcs11CallocCb );
        xResult = C_FindObjectsInit( xSession, ( CK_ATTRIBUTE_PTR ) &xFindTemplate, ulCount );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        vPkcs11Free_Stub( vPkcs11FreeCb );
        mbedtls_free_Stub( vPkcs11FreeCb );
        xResult = C_FindObjectsInit( xSession, ( CK_ATTRIBUTE_PTR ) &xFindTemplate, ulCount );
        TEST_ASSERT_EQUAL( CKR_OPERATION_ACTIVE, xResult );

        /* Clean up after the successful C_FindObjectsInit. */
        xResult = C_FindObjectsFinal( xSession );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}

/*!
 * @brief C_FindObjectsInit Bad args.
 *
 */
void test_pkcs11_C_FindObjectsInitBadArgs( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = 0;
    CK_ULONG ulCount = 1;
    CK_OBJECT_HANDLE xObject = 0;
    char * pucLabel = pkcs11configLABEL_DEVICE_CERTIFICATE_FOR_TLS;

    CK_ATTRIBUTE xFindTemplate = { CKA_LABEL, pucLabel, strlen( ( const char * ) pucLabel ) };

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        xResult = prvCreateCert( &xSession, &xObject );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        mbedtls_calloc_Stub( pvPkcs11CallocCb );
        vPkcs11Free_Stub( vPkcs11FreeCb );
        mbedtls_free_Stub( vPkcs11FreeCb );
        xResult = C_FindObjectsInit( xSession, NULL, ulCount );
        TEST_ASSERT_EQUAL( CKR_ARGUMENTS_BAD, xResult );

        xResult = C_FindObjectsInit( xSession, ( CK_ATTRIBUTE_PTR ) &xFindTemplate, -1 );
        TEST_ASSERT_EQUAL( CKR_ARGUMENTS_BAD, xResult );


        mbedtls_calloc_Stub( NULL );
        mbedtls_calloc_ExpectAnyArgsAndReturn( NULL );
        xResult = C_FindObjectsInit( xSession, ( CK_ATTRIBUTE_PTR ) &xFindTemplate, ulCount );
        mbedtls_calloc_Stub( pvPkcs11CallocCb );
        TEST_ASSERT_EQUAL( CKR_HOST_MEMORY, xResult );


        /* Clean up after C_FindObjectsInit. */
        xResult = C_FindObjectsFinal( xSession );
        TEST_ASSERT_EQUAL( CKR_OPERATION_NOT_INITIALIZED, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}

/* ======================  TESTING C_FindObjects  ============================ */

/*!
 * @brief C_FindObjects happy path.
 *
 */
void test_pkcs11_C_FindObjects( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = 0;
    CK_ULONG ulCount = 1;
    CK_ULONG ulFoundCount = 0;
    CK_OBJECT_HANDLE xObject = 0;
    CK_BYTE pucBuf[] = { 1, 1, 1, 1 };
    CK_BYTE_PTR * ppucBufPtr = ( CK_BYTE_PTR * ) &pucBuf;
    CK_ULONG ulObjectLength = sizeof( pucBuf );
    char * pucLabel = pkcs11configLABEL_DEVICE_CERTIFICATE_FOR_TLS;

    CK_ATTRIBUTE xFindTemplate = { CKA_LABEL, pucLabel, strlen( ( const char * ) pucLabel ) };

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        xResult = prvCreateCert( &xSession, &xObject );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        xResult = C_FindObjectsInit( xSession, ( CK_ATTRIBUTE_PTR ) &xFindTemplate, ulCount );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        PKCS11_PAL_FindObject_IgnoreAndReturn( 1 );
        xResult = C_FindObjects( xSession, ( CK_OBJECT_HANDLE_PTR ) &xObject, 1, &ulFoundCount );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );
        TEST_ASSERT_EQUAL( 1, ulFoundCount );

        /* Clean up after C_FindObjectsInit. */
        vPkcs11Free_Stub( vPkcs11FreeCb );
        mbedtls_free_Stub( vPkcs11FreeCb );
        xResult = C_FindObjectsFinal( xSession );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}

/*!
 * @brief C_FindObjects PKCS11_PAL_FindObject fails.
 *
 */
void test_pkcs11_C_FindObjectsPalFail( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = 0;
    CK_ULONG ulCount = 1;
    CK_ULONG ulFoundCount = 0;
    CK_OBJECT_HANDLE xObject = 1;
    char * pucLabel = pkcs11configLABEL_DEVICE_CERTIFICATE_FOR_TLS;

    CK_ATTRIBUTE xFindTemplate = { CKA_LABEL, pucLabel, strlen( ( const char * ) pucLabel ) };

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        xResult = C_FindObjectsInit( xSession, ( CK_ATTRIBUTE_PTR ) &xFindTemplate, ulCount );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        PKCS11_PAL_FindObject_IgnoreAndReturn( 0 );
        xResult = C_FindObjects( xSession, ( CK_OBJECT_HANDLE_PTR ) &xObject, 1, &ulFoundCount );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );
        TEST_ASSERT_EQUAL( 0, ulFoundCount );
        TEST_ASSERT_EQUAL( CK_INVALID_HANDLE, xObject );

        /* Clean up after C_FindObjectsInit. */
        vPkcs11Free_Stub( vPkcs11FreeCb );
        mbedtls_free_Stub( vPkcs11FreeCb );
        xResult = C_FindObjectsFinal( xSession );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}

/*!
 * @brief C_FindObjects bad args.
 *
 */
void test_pkcs11_C_FindObjectsBadArgs( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = 0;
    CK_ULONG ulCount = 1;
    CK_ULONG ulFoundCount = 0;
    CK_OBJECT_HANDLE xObject = 0;
    char * pucLabel = pkcs11configLABEL_DEVICE_CERTIFICATE_FOR_TLS;
    CK_BYTE pucBuf[] = { 0, 0, 0, 0 };
    CK_BYTE ** ppucBufPtr = ( CK_BYTE ** ) &pucBuf;
    CK_ULONG ulObjectLength = sizeof( pucBuf );

    CK_ATTRIBUTE xFindTemplate = { CKA_LABEL, pucLabel, strlen( ( const char * ) pucLabel ) };

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        vPkcs11Free_Stub( vPkcs11FreeCb );
        mbedtls_free_Stub( vPkcs11FreeCb );
        xResult = C_FindObjects( xSession, ( CK_OBJECT_HANDLE_PTR ) &xObject, 1, &ulFoundCount );
        TEST_ASSERT_EQUAL( CKR_OPERATION_NOT_INITIALIZED, xResult );

        xResult = C_FindObjectsInit( xSession, ( CK_ATTRIBUTE_PTR ) &xFindTemplate, ulCount );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        PKCS11_PAL_FindObject_IgnoreAndReturn( CK_INVALID_HANDLE );
        xResult = C_FindObjects( xSession, ( CK_OBJECT_HANDLE_PTR ) &xObject, 1, &ulFoundCount );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );
        TEST_ASSERT_EQUAL( 0, ulFoundCount );

        xResult = C_FindObjects( xSession, NULL, 1, &ulFoundCount );
        TEST_ASSERT_EQUAL( CKR_ARGUMENTS_BAD, xResult );
        TEST_ASSERT_EQUAL( 0, ulFoundCount );

        xResult = C_FindObjects( xSession, ( CK_OBJECT_HANDLE_PTR ) &xObject, 0, &ulFoundCount );
        TEST_ASSERT_EQUAL( CKR_ARGUMENTS_BAD, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}

/* ======================  TESTING C_FindObjectsFinal  ============================ */

/*!
 * @brief C_FindObjectsFinal happy path.
 *
 */
void test_pkcs11_C_FindObjectsFinal( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = 0;
    CK_ULONG ulCount = 1;
    CK_OBJECT_HANDLE xObject = 0;
    char * pucLabel = pkcs11configLABEL_DEVICE_CERTIFICATE_FOR_TLS;

    PKCS11_CertificateTemplate_t xCertificateTemplate = { { CKA_LABEL,
                                                            pucLabel,
                                                            strlen( ( const char * ) pucLabel ) } };

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        xResult = prvCreateCert( &xSession, &xObject );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        mbedtls_calloc_Stub( pvPkcs11CallocCb );
        xResult = C_FindObjectsInit( xSession, ( CK_ATTRIBUTE_PTR ) &xCertificateTemplate, ulCount );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        vPkcs11Free_Stub( vPkcs11FreeCb );
        mbedtls_free_Stub( vPkcs11FreeCb );
        xResult = C_FindObjectsFinal( xSession );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}
/* ======================  TESTING C_DigestInit  ============================ */

/*!
 * @brief C_DigestInit happy path.
 *
 */
void test_pkcs11_C_DigestInit( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = 0;
    CK_MECHANISM xMechanism = { 0 };

    xMechanism.mechanism = CKM_SHA256;

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        mbedtls_sha256_init_CMockIgnore();
        mbedtls_sha256_starts_ret_IgnoreAndReturn( 0 );
        xResult = C_DigestInit( xSession, &xMechanism );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}

/*!
 * @brief C_DigestInit session was closed.
 *
 */
void test_pkcs11_C_DigestInitClosedSession( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = 0;
    CK_MECHANISM xMechanism = { 0 };

    xMechanism.mechanism = CKM_SHA256;

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        prvCloseSession( &xSession );

        mbedtls_sha256_init_CMockIgnore();
        mbedtls_sha256_starts_ret_IgnoreAndReturn( 0 );
        xResult = C_DigestInit( xSession, &xMechanism );
        TEST_ASSERT_EQUAL( CKR_SESSION_HANDLE_INVALID, xResult );
    }

    prvUninitializePkcs11();
}

/*!
 * @brief C_DigestInit bad args.
 *
 */
void test_pkcs11_C_DigestInitBadArgs( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = 0;
    CK_MECHANISM xMechanism = { 0 };

    xMechanism.mechanism = CKM_SHA256;

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        xResult = C_DigestInit( xSession, NULL );
        TEST_ASSERT_EQUAL( CKR_ARGUMENTS_BAD, xResult );

        xMechanism.mechanism = ( CK_MECHANISM_TYPE ) ( -1 );
        xResult = C_DigestInit( xSession, &xMechanism );
        TEST_ASSERT_EQUAL( CKR_MECHANISM_INVALID, xResult );

        xMechanism.mechanism = CKM_SHA256;
        mbedtls_sha256_init_CMockIgnore();
        mbedtls_sha256_starts_ret_IgnoreAndReturn( 1 );
        xResult = C_DigestInit( xSession, &xMechanism );
        TEST_ASSERT_EQUAL( CKR_FUNCTION_FAILED, xResult );

        xMechanism.mechanism = CKM_SHA256;
        mbedtls_sha256_init_CMockIgnore();
        mbedtls_sha256_starts_ret_IgnoreAndReturn( 0 );
        xResult = C_DigestInit( xSession, &xMechanism );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        xResult = C_DigestInit( xSession, &xMechanism );
        TEST_ASSERT_EQUAL( CKR_OPERATION_ACTIVE, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}

/* ======================  TESTING C_DigestUpdate  ============================ */

/*!
 * @brief C_DigestUpdate happy path.
 *
 */
void test_pkcs11_C_DigestUpdate( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = 0;
    CK_MECHANISM xMechanism = { 0 };

    xMechanism.mechanism = CKM_SHA256;
    CK_BYTE pxDummyData[] = "Dummy data";

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        mbedtls_sha256_init_CMockIgnore();
        mbedtls_sha256_starts_ret_IgnoreAndReturn( 0 );
        xResult = C_DigestInit( xSession, &xMechanism );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        mbedtls_sha256_update_ret_IgnoreAndReturn( 0 );
        xResult = C_DigestUpdate( xSession, pxDummyData, sizeof( pxDummyData ) );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}

/*!
 * @brief C_DigestUpdate bad args.
 *
 */
void test_pkcs11_C_DigestUpdateBadArgs( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = 0;
    CK_MECHANISM xMechanism = { 0 };

    xMechanism.mechanism = CKM_SHA256;
    CK_BYTE pxDummyData[] = "Dummy data";

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        mbedtls_sha256_init_CMockIgnore();
        mbedtls_sha256_starts_ret_IgnoreAndReturn( 0 );
        xResult = C_DigestInit( xSession, &xMechanism );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        mbedtls_sha256_update_ret_ExpectAnyArgsAndReturn( -1 );
        mbedtls_sha256_free_CMockIgnore();
        xResult = C_DigestUpdate( xSession, pxDummyData, sizeof( pxDummyData ) );
        TEST_ASSERT_EQUAL( CKR_FUNCTION_FAILED, xResult );

        xResult = C_DigestUpdate( xSession, NULL, sizeof( pxDummyData ) );
        TEST_ASSERT_EQUAL( CKR_ARGUMENTS_BAD, xResult );

        xResult = C_DigestUpdate( xSession, pxDummyData, sizeof( pxDummyData ) );
        TEST_ASSERT_EQUAL( CKR_OPERATION_NOT_INITIALIZED, xResult );

        xResult = C_DigestInit( xSession, &xMechanism );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}
/* ======================  TESTING C_DigestFinal  ============================ */

/*!
 * @brief C_DigestFinal happy path.
 *
 */
void test_pkcs11_C_DigestFinal( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = 0;
    CK_MECHANISM xMechanism = { 0 };

    xMechanism.mechanism = CKM_SHA256;
    CK_BYTE pxDummyData[] = "Dummy data";
    CK_ULONG ulDigestLen = pkcs11SHA256_DIGEST_LENGTH;


    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        mbedtls_sha256_init_CMockIgnore();
        mbedtls_sha256_starts_ret_IgnoreAndReturn( 0 );
        xResult = C_DigestInit( xSession, &xMechanism );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        xResult = C_DigestFinal( xSession, NULL, &ulDigestLen );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );
        TEST_ASSERT_EQUAL( pkcs11SHA256_DIGEST_LENGTH, ulDigestLen );

        mbedtls_sha256_finish_ret_IgnoreAndReturn( 0 );
        xResult = C_DigestFinal( xSession, pxDummyData, &ulDigestLen );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );
        TEST_ASSERT_EQUAL( pkcs11SHA256_DIGEST_LENGTH, ulDigestLen );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}

/*!
 * @brief C_DigestFinal bad args.
 *
 */
void test_pkcs11_C_DigestFinalBadArgs( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = 0;
    CK_MECHANISM xMechanism = { 0 };

    xMechanism.mechanism = CKM_SHA256;
    CK_BYTE pxDummyData[] = "Dummy data";
    CK_ULONG ulDigestLen = pkcs11SHA256_DIGEST_LENGTH;


    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        mbedtls_sha256_free_CMockIgnore();
        xResult = C_DigestFinal( xSession, pxDummyData, &ulDigestLen );
        TEST_ASSERT_EQUAL( CKR_OPERATION_NOT_INITIALIZED, xResult );

        mbedtls_sha256_init_CMockIgnore();
        mbedtls_sha256_starts_ret_IgnoreAndReturn( 0 );
        xResult = C_DigestInit( xSession, &xMechanism );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        mbedtls_sha256_finish_ret_IgnoreAndReturn( -1 );
        xResult = C_DigestFinal( xSession, pxDummyData, &ulDigestLen );
        TEST_ASSERT_EQUAL( CKR_FUNCTION_FAILED, xResult );
        TEST_ASSERT_EQUAL( pkcs11SHA256_DIGEST_LENGTH, ulDigestLen );

        mbedtls_sha256_finish_ret_IgnoreAndReturn( -1 );
        xResult = C_DigestFinal( xSession, pxDummyData, NULL );
        TEST_ASSERT_EQUAL( CKR_ARGUMENTS_BAD, xResult );


        mbedtls_sha256_init_CMockIgnore();
        mbedtls_sha256_starts_ret_IgnoreAndReturn( 0 );
        xResult = C_DigestInit( xSession, &xMechanism );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        ulDigestLen = 0;
        xResult = C_DigestFinal( xSession, pxDummyData, &ulDigestLen );
        TEST_ASSERT_EQUAL( CKR_BUFFER_TOO_SMALL, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}
/* ======================  TESTING C_SignInit  ============================ */

/*!
 * @brief C_SignInit ECDSA happy path.
 *
 */
void test_pkcs11_C_SignInitECDSA( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = 0;
    CK_MECHANISM xMechanism = { 0 };

    xMechanism.mechanism = CKM_ECDSA;
    CK_OBJECT_HANDLE xObject = 0;

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        xResult = prvCreateEcPub( &xSession, &xObject );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        PKCS11_PAL_GetObjectValue_IgnoreAndReturn( CKR_OK );
        mbedtls_pk_free_CMockIgnore();
        mbedtls_pk_init_CMockIgnore();
        mbedtls_pk_parse_key_IgnoreAndReturn( 0 );
        PKCS11_PAL_GetObjectValueCleanup_CMockIgnore();
        xPkType = MBEDTLS_PK_ECDSA;
        xResult = C_SignInit( xSession, &xMechanism, xObject );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}

/*!
 * @brief C_SignInit ECDSA bad args.
 *
 */
void test_pkcs11_C_SignInitECDSABadArgs( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = 0;
    CK_MECHANISM xMechanism = { 0 };
    CK_OBJECT_HANDLE xObject = 0;
    CK_BBOOL xIsPrivate = CK_FALSE;

    xMechanism.mechanism = CKM_ECDSA;
    CK_OBJECT_HANDLE xKey = pkcs11configMAX_NUM_OBJECTS + 1;

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        xResult = C_SignInit( xSession, &xMechanism, xKey );
        TEST_ASSERT_EQUAL( CKR_KEY_HANDLE_INVALID, xResult );

        xResult = prvCreateEcPriv( &xSession, &xObject );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        xResult = C_SignInit( xSession, NULL, xKey );
        TEST_ASSERT_EQUAL( CKR_ARGUMENTS_BAD, xResult );

        mbedtls_pk_free_CMockIgnore();
        mbedtls_pk_init_CMockIgnore();
        mbedtls_pk_parse_key_IgnoreAndReturn( -1 );
        PKCS11_PAL_GetObjectValueCleanup_CMockIgnore();
        xResult = C_SignInit( xSession, &xMechanism, xObject );
        TEST_ASSERT_EQUAL( CKR_KEY_HANDLE_INVALID, xResult );

        xResult = C_SignInit( xSession, &xMechanism, xObject );
        TEST_ASSERT_EQUAL( CKR_KEY_HANDLE_INVALID, xResult );

        mbedtls_pk_parse_key_IgnoreAndReturn( 0 );
        xPkType = MBEDTLS_PK_RSA;
        xResult = C_SignInit( xSession, &xMechanism, xObject );
        TEST_ASSERT_EQUAL( CKR_KEY_TYPE_INCONSISTENT, xResult );

        xMechanism.mechanism = CKM_RSA_PKCS;

        mbedtls_pk_parse_key_IgnoreAndReturn( 0 );
        xPkType = MBEDTLS_PK_ECDSA;
        xResult = C_SignInit( xSession, &xMechanism, xObject );
        TEST_ASSERT_EQUAL( CKR_KEY_TYPE_INCONSISTENT, xResult );

        xMechanism.mechanism = CKM_RSA_X9_31;

        xResult = C_SignInit( xSession, &xMechanism, xObject );
        TEST_ASSERT_EQUAL( CKR_MECHANISM_INVALID, xResult );

        xMechanism.mechanism = CKM_RSA_X_509;

        xResult = C_SignInit( xSession, &xMechanism, xObject );
        TEST_ASSERT_EQUAL( CKR_MECHANISM_INVALID, xResult );

        xMechanism.mechanism = CKM_ECDSA;

        xResult = prvCreateEcPub( &xSession, &xObject );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        PKCS11_PAL_GetObjectValue_IgnoreAndReturn( CKR_KEY_HANDLE_INVALID );
        xResult = C_SignInit( xSession, &xMechanism, xObject );
        TEST_ASSERT_EQUAL( CKR_KEY_HANDLE_INVALID, xResult );

        PKCS11_PAL_GetObjectValue_ExpectAnyArgsAndReturn( CKR_OK );
        PKCS11_PAL_GetObjectValue_ReturnThruPtr_pIsPrivate( &xIsPrivate );
        xResult = C_SignInit( xSession, &xMechanism, xObject );
        TEST_ASSERT_EQUAL( CKR_KEY_TYPE_INCONSISTENT, xResult );

        PKCS11_PAL_GetObjectValue_ExpectAnyArgsAndReturn( CKR_OK );
        mock_osal_mutex_lock_ExpectAnyArgsAndReturn( -1 );
        xResult = C_SignInit( xSession, &xMechanism, xObject );
        mock_osal_mutex_lock_IgnoreAndReturn( 0 );
        TEST_ASSERT_EQUAL( CKR_CANT_LOCK, xResult );

        PKCS11_PAL_GetObjectValue_IgnoreAndReturn( CKR_OK );
        mbedtls_pk_free_CMockIgnore();
        mbedtls_pk_init_CMockIgnore();
        mbedtls_pk_parse_key_IgnoreAndReturn( 0 );
        PKCS11_PAL_GetObjectValueCleanup_CMockIgnore();
        xPkType = MBEDTLS_PK_ECDSA;
        xResult = C_SignInit( xSession, &xMechanism, xObject );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        xResult = C_SignInit( xSession, &xMechanism, xObject );
        TEST_ASSERT_EQUAL( CKR_OPERATION_ACTIVE, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}

/*!
 * @brief C_SignInit SHA256-HMAC happy path.
 *
 */
void test_pkcs11_C_SignInitSHA256HMAC( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = 0;
    CK_MECHANISM xMechanism = { 0 };

    xMechanism.mechanism = CKM_SHA256_HMAC;
    CK_OBJECT_HANDLE xObject = 0;

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        xResult = prvCreateSHA256HMAC( &xSession, &xObject );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        PKCS11_PAL_GetObjectValue_IgnoreAndReturn( CKR_OK );
        mbedtls_md_init_ExpectAnyArgs();
        mbedtls_md_info_from_type_ExpectAnyArgsAndReturn( ( const mbedtls_md_info_t * ) &xObject );
        mbedtls_md_setup_ExpectAnyArgsAndReturn( 0 );
        mbedtls_md_hmac_starts_ExpectAnyArgsAndReturn( 0 );
        PKCS11_PAL_GetObjectValueCleanup_CMockIgnore();
        xResult = C_SignInit( xSession, &xMechanism, xObject );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}

/*!
 * @brief C_SignInit AES-CMAC happy path.
 *
 */
void test_pkcs11_C_SignInitAESCMAC( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = 0;
    CK_MECHANISM xMechanism = { 0 };

    xMechanism.mechanism = CKM_AES_CMAC;
    CK_OBJECT_HANDLE xObject = 0;
    mbedtls_cipher_info_t * pxCipherInfo = ( mbedtls_cipher_info_t * ) &( xObject );

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        xResult = prvCreateAESCMAC( &xSession, &xObject );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        PKCS11_PAL_GetObjectValue_IgnoreAndReturn( CKR_OK );
        mbedtls_cipher_init_ExpectAnyArgs();
        mbedtls_cipher_info_from_type_ExpectAnyArgsAndReturn( pxCipherInfo );
        mbedtls_cipher_setup_ExpectAnyArgsAndReturn( 0 );
        mbedtls_cipher_cmac_starts_ExpectAnyArgsAndReturn( 0 );
        PKCS11_PAL_GetObjectValueCleanup_CMockIgnore();
        xResult = C_SignInit( xSession, &xMechanism, xObject );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}
/* ======================  TESTING C_Sign  ============================ */

/*!
 * @brief C_Sign ECDSA happy path.
 *
 */
void test_pkcs11_C_SignECDSA( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = CK_INVALID_HANDLE;
    CK_OBJECT_HANDLE xKey = CK_INVALID_HANDLE;
    CK_MECHANISM xMechanism = { 0 };
    mbedtls_pk_context xSignAndVerifyKey;

    CK_BYTE pxDummyData[ pkcs11SHA256_DIGEST_LENGTH ] = { 0xAA };
    CK_ULONG ulDummyDataLen = sizeof( pxDummyData );
    CK_BYTE pxDummySignature[ pkcs11ECDSA_P256_SIGNATURE_LENGTH ] = { 0xAA };
    CK_ULONG ulDummySignatureLen = sizeof( pxDummySignature );

    xSignAndVerifyKey.pk_ctx = &xResult;
    xMechanism.mechanism = CKM_ECDSA;

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        xResult = prvCreateEcPriv( &xSession, &xKey );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        PKCS11_PAL_GetObjectValue_IgnoreAndReturn( CKR_OK );
        mbedtls_pk_free_CMockIgnore();
        mbedtls_pk_init_CMockIgnore();
        mbedtls_pk_parse_key_IgnoreAndReturn( 0 );
        PKCS11_PAL_GetObjectValueCleanup_CMockIgnore();
        xPkType = MBEDTLS_PK_ECDSA;
        xResult = C_SignInit( xSession, &xMechanism, xKey );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        mbedtls_pk_sign_IgnoreAndReturn( 0 );
        mbedtls_pk_sign_ReturnThruPtr_ctx( &xSignAndVerifyKey );
        PKI_mbedTLSSignatureToPkcs11Signature_IgnoreAndReturn( 0 );
        xResult = C_Sign( xSession, pxDummyData, ulDummyDataLen, pxDummySignature, &ulDummySignatureLen );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}

/*!
 * @brief C_Sign ECDSA get size.
 *
 */
void test_pkcs11_C_SignECDSAGetSize( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = CK_INVALID_HANDLE;
    CK_OBJECT_HANDLE xKey = CK_INVALID_HANDLE;
    CK_MECHANISM xMechanism = { 0 };
    mbedtls_pk_context xSignAndVerifyKey;

    CK_BYTE pxDummyData[ pkcs11SHA256_DIGEST_LENGTH ] = { 0xAA };
    CK_ULONG ulDummyDataLen = sizeof( pxDummyData );
    CK_BYTE pxDummySignature[ pkcs11ECDSA_P256_SIGNATURE_LENGTH ] = { 0xAA };
    CK_ULONG ulDummySignatureLen = sizeof( pxDummySignature );

    xSignAndVerifyKey.pk_ctx = &xResult;
    xMechanism.mechanism = CKM_ECDSA;

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        xResult = prvCreateEcPriv( &xSession, &xKey );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        PKCS11_PAL_GetObjectValue_IgnoreAndReturn( CKR_OK );
        mbedtls_pk_free_CMockIgnore();
        mbedtls_pk_init_CMockIgnore();
        mbedtls_pk_parse_key_IgnoreAndReturn( 0 );
        PKCS11_PAL_GetObjectValueCleanup_CMockIgnore();
        xPkType = MBEDTLS_PK_ECDSA;
        xResult = C_SignInit( xSession, &xMechanism, xKey );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        mbedtls_pk_sign_IgnoreAndReturn( 0 );
        mbedtls_pk_sign_ReturnThruPtr_ctx( &xSignAndVerifyKey );
        PKI_mbedTLSSignatureToPkcs11Signature_IgnoreAndReturn( 0 );
        xResult = C_Sign( xSession, pxDummyData, ulDummyDataLen, NULL, &ulDummySignatureLen );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );
        TEST_ASSERT_EQUAL( pkcs11ECDSA_P256_SIGNATURE_LENGTH, ulDummySignatureLen );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}

/*!
 * @brief C_Sign RSA happy path.
 *
 */
void test_pkcs11_C_SignRSA( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = 0;
    CK_MECHANISM xMechanism = { 0 };
    mbedtls_pk_context xSignAndVerifyKey;

    xSignAndVerifyKey.pk_ctx = &xResult;

    xMechanism.mechanism = CKM_RSA_PKCS;
    CK_OBJECT_HANDLE xKey = 0;
    CK_BYTE pxDummyData[ pkcs11RSA_SIGNATURE_INPUT_LENGTH ] = { 0xAA };
    CK_ULONG ulDummyDataLen = sizeof( pxDummyData );
    CK_BYTE pxDummySignature[ pkcs11RSA_2048_SIGNATURE_LENGTH ] = { 0xAA };
    CK_ULONG ulDummySignatureLen = sizeof( pxDummySignature );

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        xResult = prvCreateRsaPriv( &xSession, &xKey );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        PKCS11_PAL_GetObjectValue_IgnoreAndReturn( CKR_OK );
        mbedtls_pk_free_CMockIgnore();
        mbedtls_pk_init_CMockIgnore();
        mbedtls_pk_parse_key_IgnoreAndReturn( 0 );
        PKCS11_PAL_GetObjectValueCleanup_CMockIgnore();
        xPkType = MBEDTLS_PK_RSA;
        xResult = C_SignInit( xSession, &xMechanism, xKey );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        mbedtls_pk_sign_IgnoreAndReturn( 0 );
        mbedtls_pk_sign_ReturnThruPtr_ctx( &xSignAndVerifyKey );
        PKI_mbedTLSSignatureToPkcs11Signature_IgnoreAndReturn( 0 );
        xResult = C_Sign( xSession, pxDummyData, ulDummyDataLen, pxDummySignature, &ulDummySignatureLen );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}

/*!
 * @brief C_Sign SHA256-HMAC happy path.
 *
 */
void test_pkcs11_C_SignSHA256HMAC( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = CK_INVALID_HANDLE;
    CK_OBJECT_HANDLE xKey = CK_INVALID_HANDLE;
    CK_MECHANISM xMechanism = { 0 };
    mbedtls_pk_context xSignAndVerifyKey;

    CK_BYTE pxDummyData[ pkcs11SHA256_DIGEST_LENGTH ] = { 0xAA };
    CK_ULONG ulDummyDataLen = sizeof( pxDummyData );
    CK_BYTE pxDummySignature[ pkcs11SHA256_DIGEST_LENGTH ] = { 0xAA };
    CK_ULONG ulDummySignatureLen = sizeof( pxDummySignature );

    xSignAndVerifyKey.pk_ctx = &xResult;
    xMechanism.mechanism = CKM_SHA256_HMAC;

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        xResult = prvCreateSHA256HMAC( &xSession, &xKey );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        PKCS11_PAL_GetObjectValue_IgnoreAndReturn( CKR_OK );
        mbedtls_md_init_ExpectAnyArgs();
        mbedtls_md_info_from_type_ExpectAnyArgsAndReturn( ( const mbedtls_md_info_t * ) &xMechanism );
        mbedtls_md_setup_ExpectAnyArgsAndReturn( 0 );
        mbedtls_md_hmac_starts_ExpectAnyArgsAndReturn( 0 );
        PKCS11_PAL_GetObjectValueCleanup_CMockIgnore();
        xResult = C_SignInit( xSession, &xMechanism, xKey );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        mbedtls_md_hmac_update_ExpectAnyArgsAndReturn( 0 );
        mbedtls_md_hmac_finish_ExpectAnyArgsAndReturn( 0 );
        mbedtls_md_free_CMockIgnore();
        xResult = C_Sign( xSession, pxDummyData, ulDummyDataLen, pxDummySignature, &ulDummySignatureLen );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}

/*!
 * @brief C_Sign SHA256-HMAC update fail.
 *
 */
void test_pkcs11_C_SignSHA256HMACUpdateFail( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = CK_INVALID_HANDLE;
    CK_OBJECT_HANDLE xKey = CK_INVALID_HANDLE;
    CK_MECHANISM xMechanism = { 0 };
    mbedtls_pk_context xSignAndVerifyKey;

    CK_BYTE pxDummyData[ pkcs11SHA256_DIGEST_LENGTH ] = { 0xAA };
    CK_ULONG ulDummyDataLen = sizeof( pxDummyData );
    CK_BYTE pxDummySignature[ pkcs11SHA256_DIGEST_LENGTH ] = { 0xAA };
    CK_ULONG ulDummySignatureLen = sizeof( pxDummySignature );

    xSignAndVerifyKey.pk_ctx = &xResult;
    xMechanism.mechanism = CKM_SHA256_HMAC;

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        xResult = prvCreateSHA256HMAC( &xSession, &xKey );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        PKCS11_PAL_GetObjectValue_IgnoreAndReturn( CKR_OK );
        mbedtls_md_init_ExpectAnyArgs();
        mbedtls_md_info_from_type_ExpectAnyArgsAndReturn( ( const mbedtls_md_info_t * ) &xMechanism );
        mbedtls_md_setup_ExpectAnyArgsAndReturn( 0 );
        mbedtls_md_hmac_starts_ExpectAnyArgsAndReturn( 0 );
        PKCS11_PAL_GetObjectValueCleanup_CMockIgnore();
        xResult = C_SignInit( xSession, &xMechanism, xKey );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        mbedtls_md_hmac_update_ExpectAnyArgsAndReturn( -1 );
        mbedtls_md_free_CMockIgnore();
        xResult = C_Sign( xSession, pxDummyData, ulDummyDataLen, pxDummySignature, &ulDummySignatureLen );
        TEST_ASSERT_EQUAL( CKR_FUNCTION_FAILED, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}

/*!
 * @brief C_Sign AES-CMAC happy path.
 *
 */
void test_pkcs11_C_SignAESCMAC( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = CK_INVALID_HANDLE;
    CK_OBJECT_HANDLE xKey = CK_INVALID_HANDLE;
    CK_MECHANISM xMechanism = { 0 };
    mbedtls_pk_context xSignAndVerifyKey;

    CK_BYTE pxDummyData[ pkcs11AES_CMAC_SIGNATURE_LENGTH ] = { 0xAA };
    CK_ULONG ulDummyDataLen = sizeof( pxDummyData );
    CK_BYTE pxDummySignature[ pkcs11AES_CMAC_SIGNATURE_LENGTH ] = { 0xAA };
    CK_ULONG ulDummySignatureLen = sizeof( pxDummySignature );

    xSignAndVerifyKey.pk_ctx = &xResult;
    xMechanism.mechanism = CKM_AES_CMAC;

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        xResult = prvCreateAESCMAC( &xSession, &xKey );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        PKCS11_PAL_GetObjectValue_IgnoreAndReturn( CKR_OK );
        mbedtls_cipher_init_ExpectAnyArgs();
        mbedtls_cipher_info_from_type_ExpectAnyArgsAndReturn( ( const mbedtls_md_info_t * ) &xMechanism );
        mbedtls_cipher_setup_ExpectAnyArgsAndReturn( 0 );
        mbedtls_cipher_cmac_starts_ExpectAnyArgsAndReturn( 0 );
        PKCS11_PAL_GetObjectValueCleanup_CMockIgnore();
        xResult = C_SignInit( xSession, &xMechanism, xKey );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        mbedtls_cipher_cmac_update_ExpectAnyArgsAndReturn( 0 );
        mbedtls_cipher_cmac_finish_ExpectAnyArgsAndReturn( 0 );
        mbedtls_cipher_free_CMockIgnore();
        xResult = C_Sign( xSession, pxDummyData, ulDummyDataLen, pxDummySignature, &ulDummySignatureLen );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}

/*!
 * @brief C_Sign AES-CMAC update fail.
 *
 */
void test_pkcs11_C_SignAESCMACUpdateFail( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = CK_INVALID_HANDLE;
    CK_OBJECT_HANDLE xKey = CK_INVALID_HANDLE;
    CK_MECHANISM xMechanism = { 0 };
    mbedtls_pk_context xSignAndVerifyKey;

    CK_BYTE pxDummyData[ pkcs11AES_CMAC_SIGNATURE_LENGTH ] = { 0xAA };
    CK_ULONG ulDummyDataLen = sizeof( pxDummyData );
    CK_BYTE pxDummySignature[ pkcs11AES_CMAC_SIGNATURE_LENGTH ] = { 0xAA };
    CK_ULONG ulDummySignatureLen = sizeof( pxDummySignature );

    xSignAndVerifyKey.pk_ctx = &xResult;
    xMechanism.mechanism = CKM_AES_CMAC;

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        xResult = prvCreateAESCMAC( &xSession, &xKey );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        PKCS11_PAL_GetObjectValue_IgnoreAndReturn( CKR_OK );
        mbedtls_cipher_init_ExpectAnyArgs();
        mbedtls_cipher_info_from_type_ExpectAnyArgsAndReturn( ( const mbedtls_md_info_t * ) &xMechanism );
        mbedtls_cipher_setup_ExpectAnyArgsAndReturn( 0 );
        mbedtls_cipher_cmac_starts_ExpectAnyArgsAndReturn( 0 );
        PKCS11_PAL_GetObjectValueCleanup_CMockIgnore();
        xResult = C_SignInit( xSession, &xMechanism, xKey );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        mbedtls_cipher_cmac_update_ExpectAnyArgsAndReturn( -1 );
        mbedtls_cipher_free_CMockIgnore();
        xResult = C_Sign( xSession, pxDummyData, ulDummyDataLen, pxDummySignature, &ulDummySignatureLen );
        TEST_ASSERT_EQUAL( CKR_FUNCTION_FAILED, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}

/*!
 * @brief C_Sign ECDSA no preceding C_SignInit call.
 *
 */
void test_pkcs11_C_SignNoInit( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = 0;

    CK_BYTE pxDummyData[ pkcs11SHA256_DIGEST_LENGTH ] = { 0xAA };
    CK_ULONG ulDummyDataLen = sizeof( pxDummyData );
    CK_BYTE pxDummySignature[ pkcs11ECDSA_P256_SIGNATURE_LENGTH ] = { 0xAA };
    CK_ULONG ulDummySignatureLen = sizeof( pxDummySignature );

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        xResult = C_Sign( xSession, pxDummyData, ulDummyDataLen, pxDummySignature, &ulDummySignatureLen );
        TEST_ASSERT_EQUAL( CKR_OPERATION_NOT_INITIALIZED, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}

/*!
 * @brief C_Sign Bad args.
 *
 */
void test_pkcs11_C_SignBadArgs( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = CK_INVALID_HANDLE;
    CK_MECHANISM xMechanism = { 0 };
    mbedtls_pk_context xSignAndVerifyKey;

    xSignAndVerifyKey.pk_ctx = &xResult;

    xMechanism.mechanism = CKM_ECDSA;
    CK_OBJECT_HANDLE xKey = CK_INVALID_HANDLE;
    CK_BYTE pxDummyData[ pkcs11SHA256_DIGEST_LENGTH ] = { 0xAA };
    CK_ULONG ulDummyDataLen = sizeof( pxDummyData );
    CK_BYTE pxDummySignature[ pkcs11ECDSA_P256_SIGNATURE_LENGTH ] = { 0xAA };
    CK_ULONG ulDummySignatureLen = sizeof( pxDummySignature );

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        xResult = prvCreateEcPriv( &xSession, &xKey );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        PKCS11_PAL_GetObjectValue_IgnoreAndReturn( CKR_OK );
        mbedtls_pk_free_CMockIgnore();
        mbedtls_pk_init_CMockIgnore();
        mbedtls_pk_parse_key_IgnoreAndReturn( 0 );
        PKCS11_PAL_GetObjectValueCleanup_CMockIgnore();
        xPkType = MBEDTLS_PK_ECDSA;
        xResult = C_SignInit( xSession, &xMechanism, xKey );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        mbedtls_pk_sign_IgnoreAndReturn( -1 );
        xResult = C_Sign( xSession, pxDummyData, ulDummyDataLen, pxDummySignature, &ulDummySignatureLen );
        TEST_ASSERT_EQUAL( CKR_FUNCTION_FAILED, xResult );

        xResult = C_SignInit( xSession, &xMechanism, xKey );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        mbedtls_pk_parse_key_IgnoreAndReturn( 0 );
        mbedtls_pk_sign_IgnoreAndReturn( 0 );
        mbedtls_pk_sign_ReturnThruPtr_ctx( &xSignAndVerifyKey );
        PKI_mbedTLSSignatureToPkcs11Signature_IgnoreAndReturn( -1 );
        xResult = C_Sign( xSession, pxDummyData, ulDummyDataLen, pxDummySignature, &ulDummySignatureLen );
        TEST_ASSERT_EQUAL( CKR_FUNCTION_FAILED, xResult );

        xResult = C_Sign( xSession, pxDummyData, ulDummyDataLen, pxDummySignature, NULL );
        TEST_ASSERT_EQUAL( CKR_ARGUMENTS_BAD, xResult );

        xResult = C_SignInit( xSession, &xMechanism, xKey );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        ulDummySignatureLen = 0;
        xResult = C_Sign( xSession, pxDummyData, ulDummyDataLen, pxDummySignature, &ulDummySignatureLen );
        TEST_ASSERT_EQUAL( CKR_BUFFER_TOO_SMALL, xResult );

        ulDummySignatureLen = sizeof( pxDummySignature );
        xResult = C_Sign( xSession, pxDummyData, 0, pxDummySignature, &ulDummySignatureLen );
        TEST_ASSERT_EQUAL( CKR_DATA_LEN_RANGE, xResult );

        xResult = C_SignInit( xSession, &xMechanism, xKey );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        ulDummySignatureLen = sizeof( pxDummySignature );
        mock_osal_mutex_lock_Stub( NULL );
        mock_osal_mutex_lock_ExpectAnyArgsAndReturn( -1 );
        xResult = C_Sign( xSession, pxDummyData, ulDummyDataLen, pxDummySignature, &ulDummySignatureLen );
        TEST_ASSERT_EQUAL( CKR_CANT_LOCK, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}

/* ======================  TESTING C_VerifyInit  ============================ */

/*!
 * @brief C_VerifyInit ECDSA happy path.
 *
 */
void test_pkcs11_C_VerifyInitECDSA( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = 0;
    CK_OBJECT_HANDLE xObject = 0;
    CK_MECHANISM xMechanism = { 0 };
    mbedtls_pk_context xVerifyKey = { NULL, &xResult };

    xMechanism.mechanism = CKM_ECDSA;
    CK_BBOOL xIsPrivate = CK_FALSE;

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        xResult = prvCreateEcPub( &xSession, &xObject );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        PKCS11_PAL_GetObjectValue_ExpectAnyArgsAndReturn( CKR_OK );
        PKCS11_PAL_GetObjectValue_ReturnThruPtr_pIsPrivate( &xIsPrivate );
        mbedtls_pk_free_CMockIgnore();
        mbedtls_pk_init_ExpectAnyArgs();
        mbedtls_pk_init_ReturnThruPtr_ctx( &xVerifyKey );
        mbedtls_pk_parse_public_key_IgnoreAndReturn( 0 );
        PKCS11_PAL_GetObjectValueCleanup_CMockIgnore();
        xPkType = MBEDTLS_PK_ECDSA;
        xResult = C_VerifyInit( xSession, &xMechanism, xObject );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}

/*!
 * @brief C_VerifyInit SHA256-HMAC happy path.
 *
 */
void test_pkcs11_C_VerifyInitSHA256HMAC( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = 0;
    CK_OBJECT_HANDLE xObject = 0;
    CK_MECHANISM xMechanism = { 0 };

    xMechanism.mechanism = CKM_SHA256_HMAC;
    CK_BBOOL xIsPrivate = CK_FALSE;

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        xResult = prvCreateSHA256HMAC( &xSession, &xObject );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        PKCS11_PAL_GetObjectValue_ExpectAnyArgsAndReturn( CKR_OK );
        PKCS11_PAL_GetObjectValue_ReturnThruPtr_pIsPrivate( &xIsPrivate );
        mbedtls_md_init_CMockIgnore();
        mbedtls_md_info_from_type_ExpectAnyArgsAndReturn( &xObject );
        mbedtls_md_setup_ExpectAnyArgsAndReturn( 0 );
        mbedtls_md_hmac_starts_ExpectAnyArgsAndReturn( 0 );
        PKCS11_PAL_GetObjectValueCleanup_CMockIgnore();
        xResult = C_VerifyInit( xSession, &xMechanism, xObject );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}

/*!
 * @brief C_VerifyInit SHA256-HMAC MD info fails
 *
 */
void test_pkcs11_C_VerifyInitSHA256HMACMDInfoFail( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = 0;
    CK_OBJECT_HANDLE xObject = 0;
    CK_MECHANISM xMechanism = { 0 };

    xMechanism.mechanism = CKM_SHA256_HMAC;
    CK_BBOOL xIsPrivate = CK_FALSE;

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        xResult = prvCreateSHA256HMAC( &xSession, &xObject );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        PKCS11_PAL_GetObjectValue_ExpectAnyArgsAndReturn( CKR_OK );
        PKCS11_PAL_GetObjectValue_ReturnThruPtr_pIsPrivate( &xIsPrivate );
        mbedtls_md_init_CMockIgnore();
        mbedtls_md_info_from_type_ExpectAnyArgsAndReturn( NULL );
        mbedtls_md_free_CMockIgnore();
        PKCS11_PAL_GetObjectValueCleanup_CMockIgnore();

        xResult = C_VerifyInit( xSession, &xMechanism, xObject );
        TEST_ASSERT_EQUAL( CKR_FUNCTION_FAILED, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}

/*!
 * @brief C_VerifyInit SHA256-HMAC MD setup fails
 *
 */
void test_pkcs11_C_VerifyInitSHA256HMACMDSetupFail( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = 0;
    CK_OBJECT_HANDLE xObject = 0;
    CK_MECHANISM xMechanism = { 0 };

    xMechanism.mechanism = CKM_SHA256_HMAC;
    CK_BBOOL xIsPrivate = CK_FALSE;

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        xResult = prvCreateSHA256HMAC( &xSession, &xObject );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        PKCS11_PAL_GetObjectValue_ExpectAnyArgsAndReturn( CKR_OK );
        PKCS11_PAL_GetObjectValue_ReturnThruPtr_pIsPrivate( &xIsPrivate );
        mbedtls_md_init_CMockIgnore();
        mbedtls_md_info_from_type_ExpectAnyArgsAndReturn( ( mbedtls_md_info_t * ) &xObject );
        mbedtls_md_setup_ExpectAnyArgsAndReturn( -1 );
        mbedtls_md_free_CMockIgnore();
        PKCS11_PAL_GetObjectValueCleanup_CMockIgnore();
        xResult = C_VerifyInit( xSession, &xMechanism, xObject );
        TEST_ASSERT_EQUAL( CKR_KEY_HANDLE_INVALID, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}

/*!
 * @brief C_VerifyInit SHA256-HMAC MD starts fails
 *
 */
void test_pkcs11_C_VerifyInitSHA256HMACMDsStartsFail( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = 0;
    CK_OBJECT_HANDLE xObject = 0;
    CK_MECHANISM xMechanism = { 0 };

    xMechanism.mechanism = CKM_SHA256_HMAC;
    CK_BBOOL xIsPrivate = CK_FALSE;

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        xResult = prvCreateSHA256HMAC( &xSession, &xObject );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        PKCS11_PAL_GetObjectValue_ExpectAnyArgsAndReturn( CKR_OK );
        PKCS11_PAL_GetObjectValue_ReturnThruPtr_pIsPrivate( &xIsPrivate );
        mbedtls_md_init_CMockIgnore();
        mbedtls_md_info_from_type_ExpectAnyArgsAndReturn( ( mbedtls_md_info_t * ) &xObject );
        mbedtls_md_setup_ExpectAnyArgsAndReturn( 0 );
        mbedtls_md_hmac_starts_ExpectAnyArgsAndReturn( -1 );
        mbedtls_md_free_CMockIgnore();
        PKCS11_PAL_GetObjectValueCleanup_CMockIgnore();
        xResult = C_VerifyInit( xSession, &xMechanism, xObject );
        TEST_ASSERT_EQUAL( CKR_KEY_HANDLE_INVALID, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}

/*!
 * @brief C_VerifyInit SHA256-HMAC MD mutex lock failure
 *
 */
void test_pkcs11_C_VerifyInitSHA256HMACMDLockFail( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = 0;
    CK_OBJECT_HANDLE xObject = 0;
    CK_MECHANISM xMechanism = { 0 };

    xMechanism.mechanism = CKM_SHA256_HMAC;
    CK_BBOOL xIsPrivate = CK_FALSE;

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        xResult = prvCreateSHA256HMAC( &xSession, &xObject );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        mbedtls_md_info_from_type_IgnoreAndReturn( 1 );
        PKCS11_PAL_GetObjectValue_IgnoreAndReturn( CKR_OK );
        mock_osal_mutex_lock_IgnoreAndReturn( -1 );
        PKCS11_PAL_GetObjectValueCleanup_CMockIgnore();
        xResult = C_VerifyInit( xSession, &xMechanism, xObject );
        TEST_ASSERT_EQUAL( CKR_CANT_LOCK, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}

/*!
 * @brief C_VerifyInit AES-CMAC happy path.
 *
 */
void test_pkcs11_C_VerifyInitAESCMAC( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = 0;
    CK_OBJECT_HANDLE xObject = 0;
    CK_MECHANISM xMechanism = { 0 };

    xMechanism.mechanism = CKM_AES_CMAC;
    CK_BBOOL xIsPrivate = CK_FALSE;

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        xResult = prvCreateAESCMAC( &xSession, &xObject );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        PKCS11_PAL_GetObjectValue_ExpectAnyArgsAndReturn( CKR_OK );
        PKCS11_PAL_GetObjectValue_ReturnThruPtr_pIsPrivate( &xIsPrivate );
        mbedtls_cipher_init_CMockIgnore();
        mbedtls_cipher_info_from_type_ExpectAnyArgsAndReturn( &xObject );
        mbedtls_cipher_setup_ExpectAnyArgsAndReturn( 0 );
        mbedtls_cipher_cmac_starts_ExpectAnyArgsAndReturn( 0 );
        PKCS11_PAL_GetObjectValueCleanup_CMockIgnore();
        xResult = C_VerifyInit( xSession, &xMechanism, xObject );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}

/*!
 * @brief C_VerifyInit AES-CMAC Cipher info fails
 *
 */
void test_pkcs11_C_VerifyInitAESCMACCipherInfoFail( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = 0;
    CK_OBJECT_HANDLE xObject = 0;
    CK_MECHANISM xMechanism = { 0 };

    xMechanism.mechanism = CKM_AES_CMAC;
    CK_BBOOL xIsPrivate = CK_FALSE;

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        xResult = prvCreateAESCMAC( &xSession, &xObject );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        PKCS11_PAL_GetObjectValue_ExpectAnyArgsAndReturn( CKR_OK );
        PKCS11_PAL_GetObjectValue_ReturnThruPtr_pIsPrivate( &xIsPrivate );
        mbedtls_cipher_init_CMockIgnore();
        mbedtls_cipher_info_from_type_ExpectAnyArgsAndReturn( NULL );
        mbedtls_cipher_free_CMockIgnore();
        PKCS11_PAL_GetObjectValueCleanup_CMockIgnore();

        xResult = C_VerifyInit( xSession, &xMechanism, xObject );
        TEST_ASSERT_EQUAL( CKR_FUNCTION_FAILED, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}

/*!
 * @brief C_VerifyInit AES-CMAC Cipher setup fails
 *
 */
void test_pkcs11_C_VerifyInitAESCMACCipherSetupFail( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = 0;
    CK_OBJECT_HANDLE xObject = 0;
    CK_MECHANISM xMechanism = { 0 };

    xMechanism.mechanism = CKM_AES_CMAC;
    CK_BBOOL xIsPrivate = CK_FALSE;

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        xResult = prvCreateAESCMAC( &xSession, &xObject );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        PKCS11_PAL_GetObjectValue_ExpectAnyArgsAndReturn( CKR_OK );
        PKCS11_PAL_GetObjectValue_ReturnThruPtr_pIsPrivate( &xIsPrivate );
        mbedtls_cipher_init_CMockIgnore();
        mbedtls_cipher_info_from_type_ExpectAnyArgsAndReturn( ( mbedtls_md_info_t * ) &xObject );
        mbedtls_cipher_setup_ExpectAnyArgsAndReturn( -1 );
        mbedtls_cipher_free_CMockIgnore();
        PKCS11_PAL_GetObjectValueCleanup_CMockIgnore();
        xResult = C_VerifyInit( xSession, &xMechanism, xObject );
        TEST_ASSERT_EQUAL( CKR_KEY_HANDLE_INVALID, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}


/*!
 * @brief C_VerifyInit AES-CMAC Cipher starts fails
 *
 */
void test_pkcs11_C_VerifyInitAESCMACCipherStartsFail( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = 0;
    CK_OBJECT_HANDLE xObject = 0;
    CK_MECHANISM xMechanism = { 0 };

    xMechanism.mechanism = CKM_AES_CMAC;
    CK_BBOOL xIsPrivate = CK_FALSE;

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        xResult = prvCreateAESCMAC( &xSession, &xObject );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        PKCS11_PAL_GetObjectValue_ExpectAnyArgsAndReturn( CKR_OK );
        PKCS11_PAL_GetObjectValue_ReturnThruPtr_pIsPrivate( &xIsPrivate );
        mbedtls_cipher_init_CMockIgnore();
        mbedtls_cipher_info_from_type_ExpectAnyArgsAndReturn( ( mbedtls_md_info_t * ) &xObject );
        mbedtls_cipher_setup_ExpectAnyArgsAndReturn( 0 );
        mbedtls_cipher_cmac_starts_ExpectAnyArgsAndReturn( -1 );
        mbedtls_cipher_free_CMockIgnore();
        PKCS11_PAL_GetObjectValueCleanup_CMockIgnore();
        xResult = C_VerifyInit( xSession, &xMechanism, xObject );
        TEST_ASSERT_EQUAL( CKR_KEY_HANDLE_INVALID, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}

/*!
 * @brief C_VerifyInit AES-CMAC Cipher mutex lock failure
 *
 */
void test_pkcs11_C_VerifyInitAESCMACCipherLockFail( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = 0;
    CK_OBJECT_HANDLE xObject = 0;
    CK_MECHANISM xMechanism = { 0 };

    xMechanism.mechanism = CKM_AES_CMAC;
    CK_BBOOL xIsPrivate = CK_FALSE;

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        xResult = prvCreateAESCMAC( &xSession, &xObject );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        mbedtls_cipher_info_from_type_IgnoreAndReturn( 1 );
        PKCS11_PAL_GetObjectValue_IgnoreAndReturn( CKR_OK );
        mock_osal_mutex_lock_IgnoreAndReturn( -1 );
        PKCS11_PAL_GetObjectValueCleanup_CMockIgnore();
        xResult = C_VerifyInit( xSession, &xMechanism, xObject );
        TEST_ASSERT_EQUAL( CKR_CANT_LOCK, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}

/*!
 * @brief C_VerifyInit ECDSA public key API failed, private key API success.
 *
 */
void test_pkcs11_C_VerifyInitECDSAPriv( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = 0;
    CK_OBJECT_HANDLE xObject = 0;
    CK_MECHANISM xMechanism = { 0 };
    mbedtls_pk_context xVerifyKey = { NULL, &xResult };

    xMechanism.mechanism = CKM_ECDSA;
    CK_BBOOL xIsPrivate = CK_FALSE;

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        xResult = prvCreateEcPub( &xSession, &xObject );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        PKCS11_PAL_GetObjectValue_ExpectAnyArgsAndReturn( CKR_OK );
        PKCS11_PAL_GetObjectValue_ReturnThruPtr_pIsPrivate( &xIsPrivate );
        mbedtls_pk_free_CMockIgnore();
        mbedtls_pk_init_ExpectAnyArgs();
        mbedtls_pk_init_ReturnThruPtr_ctx( &xVerifyKey );
        mbedtls_pk_parse_public_key_IgnoreAndReturn( -1 );
        mbedtls_pk_parse_key_IgnoreAndReturn( 0 );
        PKCS11_PAL_GetObjectValueCleanup_CMockIgnore();
        xPkType = MBEDTLS_PK_ECDSA;
        xResult = C_VerifyInit( xSession, &xMechanism, xObject );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}

/*!
 * @brief C_VerifyInit ECDSA bad args.
 *
 */
void test_pkcs11_C_VerifyInitBadArgs( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = 0;
    CK_OBJECT_HANDLE xObject = 0;
    CK_MECHANISM xMechanism = { 0 };

    xMechanism.mechanism = CKM_ECDSA;
    CK_BBOOL xIsPrivate = CK_TRUE;

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        xResult = prvCreateEcPub( &xSession, &xObject );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        xResult = C_VerifyInit( xSession, NULL, xObject );
        TEST_ASSERT_EQUAL( CKR_ARGUMENTS_BAD, xResult );

        PKCS11_PAL_GetObjectValue_ExpectAnyArgsAndReturn( CKR_KEY_HANDLE_INVALID );
        xResult = C_VerifyInit( xSession, &xMechanism, xObject );
        TEST_ASSERT_EQUAL( CKR_KEY_HANDLE_INVALID, xResult );

        PKCS11_PAL_GetObjectValue_ExpectAnyArgsAndReturn( CKR_OK );
        PKCS11_PAL_GetObjectValue_ReturnThruPtr_pIsPrivate( &xIsPrivate );
        PKCS11_PAL_GetObjectValueCleanup_CMockIgnore();
        xResult = C_VerifyInit( xSession, &xMechanism, xObject );
        TEST_ASSERT_EQUAL( CKR_KEY_TYPE_INCONSISTENT, xResult );

        xIsPrivate = CK_FALSE;

        PKCS11_PAL_GetObjectValue_ExpectAnyArgsAndReturn( CKR_OK );
        PKCS11_PAL_GetObjectValue_ReturnThruPtr_pIsPrivate( &xIsPrivate );
        mbedtls_pk_free_CMockIgnore();
        mbedtls_pk_init_CMockIgnore();
        mbedtls_pk_parse_public_key_IgnoreAndReturn( -1 );
        mbedtls_pk_parse_key_IgnoreAndReturn( -1 );
        xResult = C_VerifyInit( xSession, &xMechanism, xObject );
        TEST_ASSERT_EQUAL( CKR_KEY_HANDLE_INVALID, xResult );

        PKCS11_PAL_GetObjectValue_ExpectAnyArgsAndReturn( CKR_OK );
        PKCS11_PAL_GetObjectValue_ReturnThruPtr_pIsPrivate( &xIsPrivate );
        mbedtls_pk_parse_public_key_IgnoreAndReturn( 0 );
        xPkType = MBEDTLS_PK_RSA;
        xResult = C_VerifyInit( xSession, &xMechanism, xObject );
        TEST_ASSERT_EQUAL( CKR_KEY_TYPE_INCONSISTENT, xResult );

        xMechanism.mechanism = CKM_RSA_X_509;

        PKCS11_PAL_GetObjectValue_ExpectAnyArgsAndReturn( CKR_OK );
        PKCS11_PAL_GetObjectValue_ReturnThruPtr_pIsPrivate( &xIsPrivate );
        xPkType = MBEDTLS_PK_ECDSA;
        xResult = C_VerifyInit( xSession, &xMechanism, xObject );
        TEST_ASSERT_EQUAL( CKR_KEY_TYPE_INCONSISTENT, xResult );

        xMechanism.mechanism = CKM_RSA_X9_31;

        PKCS11_PAL_GetObjectValue_ExpectAnyArgsAndReturn( CKR_OK );
        PKCS11_PAL_GetObjectValue_ReturnThruPtr_pIsPrivate( &xIsPrivate );
        xResult = C_VerifyInit( xSession, &xMechanism, xObject );
        TEST_ASSERT_EQUAL( CKR_MECHANISM_INVALID, xResult );

        mock_osal_mutex_lock_IgnoreAndReturn( 1 );
        PKCS11_PAL_GetObjectValue_ExpectAnyArgsAndReturn( CKR_OK );
        PKCS11_PAL_GetObjectValue_ReturnThruPtr_pIsPrivate( &xIsPrivate );
        xResult = C_VerifyInit( xSession, &xMechanism, xObject );
        mock_osal_mutex_lock_IgnoreAndReturn( 0 );
        TEST_ASSERT_EQUAL( CKR_CANT_LOCK, xResult );

        xResult = C_VerifyInit( xSession, &xMechanism, pkcs11configMAX_NUM_OBJECTS + 2 );
        TEST_ASSERT_EQUAL( CKR_KEY_HANDLE_INVALID, xResult );

        xMechanism.mechanism = CKM_RSA_X_509;

        PKCS11_PAL_GetObjectValue_ExpectAnyArgsAndReturn( CKR_OK );
        PKCS11_PAL_GetObjectValue_ReturnThruPtr_pIsPrivate( &xIsPrivate );
        xPkType = MBEDTLS_PK_RSA;
        xResult = C_VerifyInit( xSession, &xMechanism, xObject );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        xPkType = MBEDTLS_PK_RSA;
        xResult = C_VerifyInit( xSession, &xMechanism, xObject );
        TEST_ASSERT_EQUAL( CKR_OPERATION_ACTIVE, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}
/* ======================  TESTING C_Verify  ============================ */

/*!
 * @brief C_Verify ECDSA happy path.
 *
 */
void test_pkcs11_C_VerifyECDSA( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = 0;
    CK_OBJECT_HANDLE xObject = 0;
    mbedtls_pk_context xVerifyKey = { NULL, &xResult };
    CK_MECHANISM xMechanism = { 0 };
    CK_BYTE pxDummyData[ pkcs11SHA256_DIGEST_LENGTH ] = { 0xAA };
    CK_ULONG ulDummyDataLen = sizeof( pxDummyData );
    CK_BYTE pxDummySignature[ pkcs11ECDSA_P256_SIGNATURE_LENGTH ] = { 0xAA };
    CK_ULONG ulDummySignatureLen = sizeof( pxDummySignature );

    xMechanism.mechanism = CKM_ECDSA;
    CK_BBOOL xIsPrivate = CK_FALSE;

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        xResult = prvCreateEcPub( &xSession, &xObject );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        PKCS11_PAL_GetObjectValue_ExpectAnyArgsAndReturn( CKR_OK );
        PKCS11_PAL_GetObjectValue_ReturnThruPtr_pIsPrivate( &xIsPrivate );
        mbedtls_pk_free_CMockIgnore();
        mbedtls_pk_init_ExpectAnyArgs();
        mbedtls_pk_init_ReturnThruPtr_ctx( &xVerifyKey );
        mbedtls_pk_parse_public_key_IgnoreAndReturn( 0 );
        PKCS11_PAL_GetObjectValueCleanup_CMockIgnore();
        xPkType = MBEDTLS_PK_ECDSA;
        xResult = C_VerifyInit( xSession, &xMechanism, xObject );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        mbedtls_pk_verify_IgnoreAndReturn( 0 );
        mbedtls_mpi_init_CMockIgnore();
        mbedtls_mpi_read_binary_IgnoreAndReturn( 0 );
        mbedtls_ecdsa_verify_IgnoreAndReturn( 0 );
        mbedtls_mpi_free_CMockIgnore();
        xResult = C_Verify( xSession, pxDummyData, ulDummyDataLen, pxDummySignature, ulDummySignatureLen );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}

/*!
 * @brief C_Verify ECDSA verify failure due to an invalid signature.
 *
 */
void test_pkcs11_C_VerifyECDSAInvalidSig( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = 0;
    CK_OBJECT_HANDLE xObject = 0;
    mbedtls_pk_context xVerifyKey = { NULL, &xResult };
    CK_MECHANISM xMechanism = { 0 };
    CK_BYTE pxDummyData[ pkcs11SHA256_DIGEST_LENGTH ] = { 0xAA };
    CK_ULONG ulDummyDataLen = sizeof( pxDummyData );
    CK_BYTE pxDummySignature[ pkcs11ECDSA_P256_SIGNATURE_LENGTH ] = { 0xAA };
    CK_ULONG ulDummySignatureLen = sizeof( pxDummySignature );

    xMechanism.mechanism = CKM_ECDSA;
    CK_BBOOL xIsPrivate = CK_FALSE;

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        xResult = prvCreateEcPub( &xSession, &xObject );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        PKCS11_PAL_GetObjectValue_ExpectAnyArgsAndReturn( CKR_OK );
        PKCS11_PAL_GetObjectValue_ReturnThruPtr_pIsPrivate( &xIsPrivate );
        mbedtls_pk_free_CMockIgnore();
        mbedtls_pk_init_ExpectAnyArgs();
        mbedtls_pk_init_ReturnThruPtr_ctx( &xVerifyKey );
        mbedtls_pk_parse_public_key_IgnoreAndReturn( 0 );
        PKCS11_PAL_GetObjectValueCleanup_CMockIgnore();
        xPkType = MBEDTLS_PK_ECDSA;
        xResult = C_VerifyInit( xSession, &xMechanism, xObject );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        mbedtls_pk_verify_IgnoreAndReturn( 0 );
        mbedtls_mpi_init_CMockIgnore();
        mbedtls_mpi_read_binary_IgnoreAndReturn( 0 );
        mbedtls_ecdsa_verify_IgnoreAndReturn( -1 );
        mbedtls_mpi_free_CMockIgnore();
        xResult = C_Verify( xSession, pxDummyData, ulDummyDataLen, pxDummySignature, ulDummySignatureLen );
        TEST_ASSERT_EQUAL( CKR_SIGNATURE_INVALID, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}

/*!
 * @brief C_Verify RSA happy path.
 *
 */
void test_pkcs11_C_VerifyRSA( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = CK_INVALID_HANDLE;
    CK_OBJECT_HANDLE xObject = CK_INVALID_HANDLE;
    CK_MECHANISM xMechanism = { 0 };
    CK_BYTE pxDummyData[ pkcs11RSA_2048_SIGNATURE_LENGTH ] = { 0xAA };
    CK_ULONG ulDummyDataLen = sizeof( pxDummyData );
    CK_BYTE pxDummySignature[ pkcs11RSA_2048_SIGNATURE_LENGTH ] = { 0xAA };
    CK_ULONG ulDummySignatureLen = sizeof( pxDummySignature );
    mbedtls_pk_context xMbedContext = { 0 };

    /* These just have to be not NULL so we can hit the proper path. */
    xMbedContext.pk_ctx = &xObject;
    xMbedContext.pk_info = &xSession;

    xMechanism.mechanism = CKM_RSA_X_509;
    CK_BBOOL xIsPrivate = CK_FALSE;

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        xResult = prvCreateRSAPub( &xSession, &xObject );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        mock_osal_mutex_lock_IgnoreAndReturn( 0 );
        mock_osal_mutex_unlock_IgnoreAndReturn( 0 );
        xResult = C_Verify( xSession, pxDummyData, 0, pxDummySignature, ulDummySignatureLen );
        TEST_ASSERT_EQUAL( CKR_OPERATION_NOT_INITIALIZED, xResult );

        PKCS11_PAL_GetObjectValue_ExpectAnyArgsAndReturn( CKR_OK );
        PKCS11_PAL_GetObjectValue_ReturnThruPtr_pIsPrivate( &xIsPrivate );
        mbedtls_pk_init_StopIgnore();
        mbedtls_pk_init_ExpectAnyArgs();
        mbedtls_pk_init_ReturnThruPtr_ctx( &xMbedContext );
        mbedtls_pk_parse_public_key_IgnoreAndReturn( 0 );
        PKCS11_PAL_GetObjectValueCleanup_CMockIgnore();
        xPkType = MBEDTLS_PK_RSA;
        xResult = C_VerifyInit( xSession, &xMechanism, xObject );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        mbedtls_pk_verify_IgnoreAndReturn( 0 );
        mbedtls_pk_free_CMockIgnore();
        xResult = C_Verify( xSession, pxDummyData, ulDummyDataLen, pxDummySignature, ulDummySignatureLen );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}

/*!
 * @brief C_Verify Bad args.
 *
 */
void test_pkcs11_C_VerifyBadArgs( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = 0;
    CK_OBJECT_HANDLE xObject = 0;
    CK_MECHANISM xMechanism = { 0 };
    mbedtls_pk_context xVerifyKey = { NULL, &xResult };
    CK_BYTE pxDummyData[ pkcs11SHA256_DIGEST_LENGTH ] = { 0xAA };
    CK_ULONG ulDummyDataLen = sizeof( pxDummyData );
    CK_BYTE pxDummySignature[ pkcs11ECDSA_P256_SIGNATURE_LENGTH ] = { 0xAA };
    CK_ULONG ulDummySignatureLen = sizeof( pxDummySignature );

    xMechanism.mechanism = CKM_ECDSA;
    CK_BBOOL xIsPrivate = CK_FALSE;

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        xResult = prvCreateEcPub( &xSession, &xObject );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        PKCS11_PAL_GetObjectValue_ExpectAnyArgsAndReturn( CKR_OK );
        PKCS11_PAL_GetObjectValue_ReturnThruPtr_pIsPrivate( &xIsPrivate );
        mbedtls_pk_free_CMockIgnore();
        mbedtls_pk_init_ExpectAnyArgs();
        mbedtls_pk_init_ReturnThruPtr_ctx( &xVerifyKey );
        mbedtls_pk_parse_public_key_IgnoreAndReturn( 0 );
        PKCS11_PAL_GetObjectValueCleanup_CMockIgnore();
        xPkType = MBEDTLS_PK_ECDSA;
        xResult = C_VerifyInit( xSession, &xMechanism, xObject );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );
        mbedtls_pk_init_CMockIgnore();

        xResult = C_Verify( xSession, pxDummyData, 0, pxDummySignature, ulDummySignatureLen );
        TEST_ASSERT_EQUAL( CKR_DATA_LEN_RANGE, xResult );

        PKCS11_PAL_GetObjectValue_ExpectAnyArgsAndReturn( CKR_OK );
        PKCS11_PAL_GetObjectValue_ReturnThruPtr_pIsPrivate( &xIsPrivate );
        xResult = C_VerifyInit( xSession, &xMechanism, xObject );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        xResult = C_Verify( xSession, pxDummyData, ulDummyDataLen, pxDummySignature, 0 );
        TEST_ASSERT_EQUAL( CKR_SIGNATURE_LEN_RANGE, xResult );

        PKCS11_PAL_GetObjectValue_ExpectAnyArgsAndReturn( CKR_OK );
        PKCS11_PAL_GetObjectValue_ReturnThruPtr_pIsPrivate( &xIsPrivate );
        xResult = C_VerifyInit( xSession, &xMechanism, xObject );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        mbedtls_mpi_init_CMockIgnore();
        mbedtls_mpi_read_binary_IgnoreAndReturn( -1 );
        mbedtls_ecdsa_verify_IgnoreAndReturn( 0 );
        mbedtls_mpi_free_CMockIgnore();
        xResult = C_Verify( xSession, pxDummyData, ulDummyDataLen, pxDummySignature, ulDummySignatureLen );
        TEST_ASSERT_EQUAL( CKR_SIGNATURE_INVALID, xResult );

        xMechanism.mechanism = CKM_RSA_X_509;
        xPkType = MBEDTLS_PK_RSA;
        PKCS11_PAL_GetObjectValue_ExpectAnyArgsAndReturn( CKR_OK );
        PKCS11_PAL_GetObjectValue_ReturnThruPtr_pIsPrivate( &xIsPrivate );
        xResult = C_VerifyInit( xSession, &xMechanism, xObject );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        xResult = C_Verify( xSession, pxDummyData, pkcs11RSA_2048_SIGNATURE_LENGTH, pxDummySignature, 0 );
        TEST_ASSERT_EQUAL( CKR_SIGNATURE_LEN_RANGE, xResult );

        xMechanism.mechanism = CKM_RSA_X_509;
        PKCS11_PAL_GetObjectValue_ExpectAnyArgsAndReturn( CKR_OK );
        PKCS11_PAL_GetObjectValue_ReturnThruPtr_pIsPrivate( &xIsPrivate );
        xResult = C_VerifyInit( xSession, &xMechanism, xObject );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        mock_osal_mutex_lock_IgnoreAndReturn( 1 );
        xResult = C_Verify( xSession, pxDummyData, pkcs11RSA_2048_SIGNATURE_LENGTH, pxDummySignature, pkcs11RSA_2048_SIGNATURE_LENGTH );
        TEST_ASSERT_EQUAL( CKR_CANT_LOCK, xResult );
        mock_osal_mutex_lock_IgnoreAndReturn( 0 );

        PKCS11_PAL_GetObjectValue_ExpectAnyArgsAndReturn( CKR_OK );
        PKCS11_PAL_GetObjectValue_ReturnThruPtr_pIsPrivate( &xIsPrivate );
        xResult = C_VerifyInit( xSession, &xMechanism, xObject );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        xResult = C_Verify( xSession, pxDummyData, 0, pxDummySignature, pkcs11RSA_2048_SIGNATURE_LENGTH );
        TEST_ASSERT_EQUAL( CKR_DATA_LEN_RANGE, xResult );

        PKCS11_PAL_GetObjectValue_ExpectAnyArgsAndReturn( CKR_OK );
        PKCS11_PAL_GetObjectValue_ReturnThruPtr_pIsPrivate( &xIsPrivate );
        xResult = C_VerifyInit( xSession, &xMechanism, xObject );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        mbedtls_pk_verify_IgnoreAndReturn( -1 );
        xResult = C_Verify( xSession, pxDummyData, pkcs11RSA_2048_SIGNATURE_LENGTH, pxDummySignature, pkcs11RSA_2048_SIGNATURE_LENGTH );
        TEST_ASSERT_EQUAL( CKR_SIGNATURE_INVALID, xResult );

        /* patch */
        xResult = C_Verify( xSession, NULL, pkcs11RSA_2048_SIGNATURE_LENGTH, NULL, pkcs11RSA_2048_SIGNATURE_LENGTH );
        TEST_ASSERT_EQUAL( CKR_ARGUMENTS_BAD, xResult );

        xMechanism.mechanism = CKM_ECDSA;
        xPkType = MBEDTLS_PK_ECDSA;
        PKCS11_PAL_GetObjectValue_ExpectAnyArgsAndReturn( CKR_OK );
        PKCS11_PAL_GetObjectValue_ReturnThruPtr_pIsPrivate( &xIsPrivate );
        xResult = C_VerifyInit( xSession, &xMechanism, xObject );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        mbedtls_mpi_read_binary_IgnoreAndReturn( 1 );
        xResult = C_Verify( xSession, pxDummyData, pkcs11SHA256_DIGEST_LENGTH, pxDummySignature, pkcs11ECDSA_P256_SIGNATURE_LENGTH );
        TEST_ASSERT_EQUAL( CKR_SIGNATURE_INVALID, xResult );
        mbedtls_mpi_read_binary_IgnoreAndReturn( 0 );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}

/*!
 * @brief C_Verify SHA256-HMAC happy path.
 *
 */
void test_pkcs11_C_VerifySHA256HMAC( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = CK_INVALID_HANDLE;
    CK_OBJECT_HANDLE xObject = CK_INVALID_HANDLE;
    CK_MECHANISM xMechanism = { 0 };
    CK_BYTE pxDummyData[ pkcs11SHA256_DIGEST_LENGTH ] = { 0xAA };
    CK_ULONG ulDummyDataLen = sizeof( pxDummyData );
    CK_BYTE pxDummySignature[ pkcs11SHA256_DIGEST_LENGTH ] = { 0xAA };
    CK_ULONG ulDummySignatureLen = sizeof( pxDummySignature );

    xMechanism.mechanism = CKM_SHA256_HMAC;
    CK_BBOOL xIsPrivate = CK_FALSE;

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        xResult = prvCreateSHA256HMAC( &xSession, &xObject );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        PKCS11_PAL_GetObjectValue_ExpectAnyArgsAndReturn( CKR_OK );
        PKCS11_PAL_GetObjectValue_ReturnThruPtr_pIsPrivate( &xIsPrivate );
        mbedtls_md_init_CMockIgnore();
        mbedtls_md_info_from_type_ExpectAnyArgsAndReturn( &xObject );
        mbedtls_md_setup_ExpectAnyArgsAndReturn( 0 );
        mbedtls_md_hmac_starts_ExpectAnyArgsAndReturn( 0 );
        PKCS11_PAL_GetObjectValueCleanup_CMockIgnore();
        xResult = C_VerifyInit( xSession, &xMechanism, xObject );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        mbedtls_md_hmac_update_ExpectAnyArgsAndReturn( 0 );
        mbedtls_md_hmac_finish_ExpectAnyArgsAndReturn( 0 );
        mbedtls_md_hmac_finish_ReturnThruPtr_output( pxDummySignature );
        mbedtls_md_free_CMockIgnore();
        xResult = C_Verify( xSession, pxDummyData, ulDummyDataLen, pxDummySignature, ulDummySignatureLen );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}

/*!
 * @brief C_Verify SHA256-HMAC mbedtls_md_update fail.
 *
 */
void test_pkcs11_C_VerifySHA256HMACUpdateFail( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = CK_INVALID_HANDLE;
    CK_OBJECT_HANDLE xObject = CK_INVALID_HANDLE;
    CK_MECHANISM xMechanism = { 0 };
    CK_BYTE pxDummyData[ pkcs11SHA256_DIGEST_LENGTH ] = { 0xAA };
    CK_ULONG ulDummyDataLen = sizeof( pxDummyData );
    CK_BYTE pxDummySignature[ pkcs11SHA256_DIGEST_LENGTH ] = { 0xAA };
    CK_ULONG ulDummySignatureLen = sizeof( pxDummySignature );

    xMechanism.mechanism = CKM_SHA256_HMAC;
    CK_BBOOL xIsPrivate = CK_FALSE;

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        xResult = prvCreateSHA256HMAC( &xSession, &xObject );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        PKCS11_PAL_GetObjectValue_ExpectAnyArgsAndReturn( CKR_OK );
        PKCS11_PAL_GetObjectValue_ReturnThruPtr_pIsPrivate( &xIsPrivate );
        mbedtls_md_init_CMockIgnore();
        mbedtls_md_info_from_type_ExpectAnyArgsAndReturn( &xObject );
        mbedtls_md_setup_ExpectAnyArgsAndReturn( 0 );
        mbedtls_md_hmac_starts_ExpectAnyArgsAndReturn( 0 );
        PKCS11_PAL_GetObjectValueCleanup_CMockIgnore();
        xResult = C_VerifyInit( xSession, &xMechanism, xObject );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        mbedtls_md_hmac_update_ExpectAnyArgsAndReturn( -1 );
        mbedtls_md_free_CMockIgnore();
        xResult = C_Verify( xSession, pxDummyData, ulDummyDataLen, pxDummySignature, ulDummySignatureLen );
        TEST_ASSERT_EQUAL( CKR_SIGNATURE_INVALID, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}

/*!
 * @brief C_Verify SHA256-HMAC mbedtls_md_finish fail.
 *
 */
void test_pkcs11_C_VerifySHA256HMACFinishFail( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = CK_INVALID_HANDLE;
    CK_OBJECT_HANDLE xObject = CK_INVALID_HANDLE;
    CK_MECHANISM xMechanism = { 0 };
    CK_BYTE pxDummyData[ pkcs11SHA256_DIGEST_LENGTH ] = { 0xAA };
    CK_ULONG ulDummyDataLen = sizeof( pxDummyData );
    CK_BYTE pxDummySignature[ pkcs11SHA256_DIGEST_LENGTH ] = { 0xAA };
    CK_ULONG ulDummySignatureLen = sizeof( pxDummySignature );

    xMechanism.mechanism = CKM_SHA256_HMAC;
    CK_BBOOL xIsPrivate = CK_FALSE;

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        xResult = prvCreateSHA256HMAC( &xSession, &xObject );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        PKCS11_PAL_GetObjectValue_ExpectAnyArgsAndReturn( CKR_OK );
        PKCS11_PAL_GetObjectValue_ReturnThruPtr_pIsPrivate( &xIsPrivate );
        mbedtls_md_init_CMockIgnore();
        mbedtls_md_info_from_type_ExpectAnyArgsAndReturn( &xObject );
        mbedtls_md_setup_ExpectAnyArgsAndReturn( 0 );
        mbedtls_md_hmac_starts_ExpectAnyArgsAndReturn( 0 );
        PKCS11_PAL_GetObjectValueCleanup_CMockIgnore();
        xResult = C_VerifyInit( xSession, &xMechanism, xObject );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        mbedtls_md_hmac_update_ExpectAnyArgsAndReturn( 0 );
        mbedtls_md_hmac_finish_ExpectAnyArgsAndReturn( -1 );
        mbedtls_md_free_CMockIgnore();
        xResult = C_Verify( xSession, pxDummyData, ulDummyDataLen, pxDummySignature, ulDummySignatureLen );
        TEST_ASSERT_EQUAL( CKR_SIGNATURE_INVALID, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}

/*!
 * @brief C_Verify SHA256-HMAC invalid signature.
 *
 */
void test_pkcs11_C_VerifySHA256HMACInvalidSig( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = CK_INVALID_HANDLE;
    CK_OBJECT_HANDLE xObject = CK_INVALID_HANDLE;
    CK_MECHANISM xMechanism = { 0 };
    CK_BYTE pxDummyData[ pkcs11SHA256_DIGEST_LENGTH ] = { 0xAA };
    CK_ULONG ulDummyDataLen = sizeof( pxDummyData );
    CK_BYTE pxDummySignature[ pkcs11SHA256_DIGEST_LENGTH ] = { 0xAA };
    CK_ULONG ulDummySignatureLen = sizeof( pxDummySignature );

    CK_BYTE pxBadSignature[ pkcs11SHA256_DIGEST_LENGTH ] = { 0xBB };

    xMechanism.mechanism = CKM_SHA256_HMAC;
    CK_BBOOL xIsPrivate = CK_FALSE;

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        xResult = prvCreateSHA256HMAC( &xSession, &xObject );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        PKCS11_PAL_GetObjectValue_ExpectAnyArgsAndReturn( CKR_OK );
        PKCS11_PAL_GetObjectValue_ReturnThruPtr_pIsPrivate( &xIsPrivate );
        mbedtls_md_init_CMockIgnore();
        mbedtls_md_info_from_type_ExpectAnyArgsAndReturn( &xObject );
        mbedtls_md_setup_ExpectAnyArgsAndReturn( 0 );
        mbedtls_md_hmac_starts_ExpectAnyArgsAndReturn( 0 );
        PKCS11_PAL_GetObjectValueCleanup_CMockIgnore();
        xResult = C_VerifyInit( xSession, &xMechanism, xObject );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        mbedtls_md_hmac_update_ExpectAnyArgsAndReturn( 0 );
        mbedtls_md_hmac_finish_ExpectAnyArgsAndReturn( 0 );
        mbedtls_md_hmac_finish_ReturnThruPtr_output( pxBadSignature );
        mbedtls_md_free_CMockIgnore();
        xResult = C_Verify( xSession, pxDummyData, ulDummyDataLen, pxDummySignature, ulDummySignatureLen );
        TEST_ASSERT_EQUAL( CKR_SIGNATURE_INVALID, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}

/*!
 * @brief C_Verify AES-CMAC happy path.
 *
 */
void test_pkcs11_C_VerifyAESCMAC( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = CK_INVALID_HANDLE;
    CK_OBJECT_HANDLE xObject = CK_INVALID_HANDLE;
    CK_MECHANISM xMechanism = { 0 };
    CK_BYTE pxDummyData[ pkcs11AES_CMAC_SIGNATURE_LENGTH ] = { 0xAA };
    CK_ULONG ulDummyDataLen = sizeof( pxDummyData );
    CK_BYTE pxDummySignature[ pkcs11AES_CMAC_SIGNATURE_LENGTH ] = { 0xAA };
    CK_ULONG ulDummySignatureLen = sizeof( pxDummySignature );

    xMechanism.mechanism = CKM_AES_CMAC;
    CK_BBOOL xIsPrivate = CK_FALSE;

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        xResult = prvCreateAESCMAC( &xSession, &xObject );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        PKCS11_PAL_GetObjectValue_ExpectAnyArgsAndReturn( CKR_OK );
        PKCS11_PAL_GetObjectValue_ReturnThruPtr_pIsPrivate( &xIsPrivate );
        mbedtls_cipher_init_CMockIgnore();
        mbedtls_cipher_info_from_type_ExpectAnyArgsAndReturn( &xObject );
        mbedtls_cipher_setup_ExpectAnyArgsAndReturn( 0 );
        mbedtls_cipher_cmac_starts_ExpectAnyArgsAndReturn( 0 );
        PKCS11_PAL_GetObjectValueCleanup_CMockIgnore();
        xResult = C_VerifyInit( xSession, &xMechanism, xObject );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        mbedtls_cipher_cmac_update_ExpectAnyArgsAndReturn( 0 );
        mbedtls_cipher_cmac_finish_ExpectAnyArgsAndReturn( 0 );
        mbedtls_cipher_cmac_finish_ReturnThruPtr_output( pxDummySignature );
        mbedtls_cipher_free_CMockIgnore();
        xResult = C_Verify( xSession, pxDummyData, ulDummyDataLen, pxDummySignature, ulDummySignatureLen );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}

/*!
 * @brief C_Verify AES-CMAC mbedtls_cipher_update fail.
 *
 */
void test_pkcs11_C_VerifyAESCMACCipherUpdateFail( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = CK_INVALID_HANDLE;
    CK_OBJECT_HANDLE xObject = CK_INVALID_HANDLE;
    CK_MECHANISM xMechanism = { 0 };
    CK_BYTE pxDummyData[ pkcs11AES_CMAC_SIGNATURE_LENGTH ] = { 0xAA };
    CK_ULONG ulDummyDataLen = sizeof( pxDummyData );
    CK_BYTE pxDummySignature[ pkcs11AES_CMAC_SIGNATURE_LENGTH ] = { 0xAA };
    CK_ULONG ulDummySignatureLen = sizeof( pxDummySignature );

    xMechanism.mechanism = CKM_AES_CMAC;
    CK_BBOOL xIsPrivate = CK_FALSE;

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        xResult = prvCreateAESCMAC( &xSession, &xObject );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        PKCS11_PAL_GetObjectValue_ExpectAnyArgsAndReturn( CKR_OK );
        PKCS11_PAL_GetObjectValue_ReturnThruPtr_pIsPrivate( &xIsPrivate );
        mbedtls_cipher_init_CMockIgnore();
        mbedtls_cipher_info_from_type_ExpectAnyArgsAndReturn( &xObject );
        mbedtls_cipher_setup_ExpectAnyArgsAndReturn( 0 );
        mbedtls_cipher_cmac_starts_ExpectAnyArgsAndReturn( 0 );
        PKCS11_PAL_GetObjectValueCleanup_CMockIgnore();
        xResult = C_VerifyInit( xSession, &xMechanism, xObject );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        mbedtls_cipher_cmac_update_ExpectAnyArgsAndReturn( -1 );
        mbedtls_cipher_free_CMockIgnore();
        xResult = C_Verify( xSession, pxDummyData, ulDummyDataLen, pxDummySignature, ulDummySignatureLen );
        TEST_ASSERT_EQUAL( CKR_SIGNATURE_INVALID, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}

/*!
 * @brief C_Verify AES-CMAC mbedtls_cipher_finish fail.
 *
 */
void test_pkcs11_C_VerifyAESCMACFinishFail( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = CK_INVALID_HANDLE;
    CK_OBJECT_HANDLE xObject = CK_INVALID_HANDLE;
    CK_MECHANISM xMechanism = { 0 };
    CK_BYTE pxDummyData[ pkcs11AES_CMAC_SIGNATURE_LENGTH ] = { 0xAA };
    CK_ULONG ulDummyDataLen = sizeof( pxDummyData );
    CK_BYTE pxDummySignature[ pkcs11AES_CMAC_SIGNATURE_LENGTH ] = { 0xAA };
    CK_ULONG ulDummySignatureLen = sizeof( pxDummySignature );

    xMechanism.mechanism = CKM_AES_CMAC;
    CK_BBOOL xIsPrivate = CK_FALSE;

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        xResult = prvCreateAESCMAC( &xSession, &xObject );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        PKCS11_PAL_GetObjectValue_ExpectAnyArgsAndReturn( CKR_OK );
        PKCS11_PAL_GetObjectValue_ReturnThruPtr_pIsPrivate( &xIsPrivate );
        mbedtls_cipher_init_CMockIgnore();
        mbedtls_cipher_info_from_type_ExpectAnyArgsAndReturn( &xObject );
        mbedtls_cipher_setup_ExpectAnyArgsAndReturn( 0 );
        mbedtls_cipher_cmac_starts_ExpectAnyArgsAndReturn( 0 );
        PKCS11_PAL_GetObjectValueCleanup_CMockIgnore();
        xResult = C_VerifyInit( xSession, &xMechanism, xObject );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        mbedtls_cipher_cmac_update_ExpectAnyArgsAndReturn( 0 );
        mbedtls_cipher_cmac_finish_ExpectAnyArgsAndReturn( -1 );
        mbedtls_cipher_free_CMockIgnore();
        xResult = C_Verify( xSession, pxDummyData, ulDummyDataLen, pxDummySignature, ulDummySignatureLen );
        TEST_ASSERT_EQUAL( CKR_SIGNATURE_INVALID, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}

/*!
 * @brief C_Verify AES-CMAC invalid signature.
 *
 */
void test_pkcs11_C_VerifyAESCMACInvalidSig( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = CK_INVALID_HANDLE;
    CK_OBJECT_HANDLE xObject = CK_INVALID_HANDLE;
    CK_MECHANISM xMechanism = { 0 };
    CK_BYTE pxDummyData[ pkcs11AES_CMAC_SIGNATURE_LENGTH ] = { 0xAA };
    CK_ULONG ulDummyDataLen = sizeof( pxDummyData );
    CK_BYTE pxDummySignature[ pkcs11AES_CMAC_SIGNATURE_LENGTH ] = { 0xAA };
    CK_ULONG ulDummySignatureLen = sizeof( pxDummySignature );

    CK_BYTE pxBadSignature[ pkcs11AES_CMAC_SIGNATURE_LENGTH ] = { 0xBB };

    xMechanism.mechanism = CKM_AES_CMAC;
    CK_BBOOL xIsPrivate = CK_FALSE;

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        xResult = prvCreateAESCMAC( &xSession, &xObject );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        PKCS11_PAL_GetObjectValue_ExpectAnyArgsAndReturn( CKR_OK );
        PKCS11_PAL_GetObjectValue_ReturnThruPtr_pIsPrivate( &xIsPrivate );
        mbedtls_cipher_init_CMockIgnore();
        mbedtls_cipher_info_from_type_ExpectAnyArgsAndReturn( &xObject );
        mbedtls_cipher_setup_ExpectAnyArgsAndReturn( 0 );
        mbedtls_cipher_cmac_starts_ExpectAnyArgsAndReturn( 0 );
        PKCS11_PAL_GetObjectValueCleanup_CMockIgnore();
        xResult = C_VerifyInit( xSession, &xMechanism, xObject );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        mbedtls_cipher_cmac_update_ExpectAnyArgsAndReturn( 0 );
        mbedtls_cipher_cmac_finish_ExpectAnyArgsAndReturn( 0 );
        mbedtls_cipher_cmac_finish_ReturnThruPtr_output( pxBadSignature );
        mbedtls_cipher_free_CMockIgnore();
        xResult = C_Verify( xSession, pxDummyData, ulDummyDataLen, pxDummySignature, ulDummySignatureLen );
        TEST_ASSERT_EQUAL( CKR_SIGNATURE_INVALID, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}

/* ======================  TESTING C_GenerateKeyPair  ============================ */

/*!
 * @brief C_GenerateKeyPair ECDSA happy path.
 *
 */
void test_pkcs11_C_GenerateKeyPairECDSA( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = 0;
    CK_OBJECT_HANDLE xPrivKeyHandle = 0;
    CK_OBJECT_HANDLE xPubKeyHandle = 0;

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        char * pucPublicKeyLabel = pkcs11configLABEL_DEVICE_PUBLIC_KEY_FOR_TLS;
        char * pucPrivateKeyLabel = pkcs11configLABEL_DEVICE_PRIVATE_KEY_FOR_TLS;

        CK_MECHANISM xMechanism =
        {
            CKM_EC_KEY_PAIR_GEN, NULL_PTR, 0
        };
        CK_BYTE xEcParams[] = pkcs11DER_ENCODED_OID_P256; /* prime256v1 */
        CK_KEY_TYPE xKeyType = CKK_EC;

        CK_BBOOL xTrue = CK_TRUE;
        CK_ATTRIBUTE xPublicKeyTemplate[] =
        {
            { CKA_KEY_TYPE,  &xKeyType,         sizeof( xKeyType )                           },
            { CKA_VERIFY,    &xTrue,            sizeof( xTrue )                              },
            { CKA_EC_PARAMS, xEcParams,         sizeof( xEcParams )                          },
            { CKA_LABEL,     pucPublicKeyLabel, strlen( ( const char * ) pucPublicKeyLabel ) }
        };

        CK_ATTRIBUTE xPrivateKeyTemplate[] =
        {
            { CKA_KEY_TYPE, &xKeyType,          sizeof( xKeyType )                            },
            { CKA_TOKEN,    &xTrue,             sizeof( xTrue )                               },
            { CKA_PRIVATE,  &xTrue,             sizeof( xTrue )                               },
            { CKA_SIGN,     &xTrue,             sizeof( xTrue )                               },
            { CKA_LABEL,    pucPrivateKeyLabel, strlen( ( const char * ) pucPrivateKeyLabel ) }
        };

        mbedtls_pk_init_CMockIgnore();
        mbedtls_pk_info_from_type_IgnoreAndReturn( 0 );
        mbedtls_pk_setup_IgnoreAndReturn( 0 );
        mbedtls_ecp_gen_key_IgnoreAndReturn( 0 );
        mbedtls_pk_write_pubkey_der_IgnoreAndReturn( 1 );
        PKCS11_PAL_SaveObject_IgnoreAndReturn( 1 );
        mbedtls_pk_write_key_der_IgnoreAndReturn( 1 );
        PKCS11_PAL_SaveObject_IgnoreAndReturn( 2 );
        vPkcs11Free_Stub( vPkcs11FreeCb );
        mbedtls_free_Stub( vPkcs11FreeCb );
        mbedtls_pk_free_CMockIgnore();
        xResult = C_GenerateKeyPair( xSession, &xMechanism, xPublicKeyTemplate,
                                     sizeof( xPublicKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                                     xPrivateKeyTemplate, sizeof( xPrivateKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                                     &xPubKeyHandle, &xPrivKeyHandle );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}

/*!
 * @brief C_GenerateKeyPair calls to mbed TLS fail.
 *
 */
void test_pkcs11_C_GenerateKeyPairMbedCallsFail( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = 0;
    CK_OBJECT_HANDLE xPrivKeyHandle = 0;
    CK_OBJECT_HANDLE xPubKeyHandle = 0;

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        char * pucPublicKeyLabel = pkcs11configLABEL_DEVICE_PUBLIC_KEY_FOR_TLS;
        char * pucPrivateKeyLabel = pkcs11configLABEL_DEVICE_PRIVATE_KEY_FOR_TLS;

        CK_MECHANISM xMechanism =
        {
            CKM_EC_KEY_PAIR_GEN, NULL_PTR, 0
        };
        CK_BYTE xEcParams[] = pkcs11DER_ENCODED_OID_P256; /* prime256v1 */
        CK_KEY_TYPE xKeyType = CKK_EC;

        CK_BBOOL xTrue = CK_TRUE;
        CK_ATTRIBUTE xPublicKeyTemplate[] =
        {
            { CKA_KEY_TYPE,  &xKeyType,         sizeof( xKeyType )                           },
            { CKA_VERIFY,    &xTrue,            sizeof( xTrue )                              },
            { CKA_EC_PARAMS, xEcParams,         sizeof( xEcParams )                          },
            { CKA_LABEL,     pucPublicKeyLabel, strlen( ( const char * ) pucPublicKeyLabel ) }
        };

        CK_ATTRIBUTE xPrivateKeyTemplate[] =
        {
            { CKA_KEY_TYPE, &xKeyType,          sizeof( xKeyType )                            },
            { CKA_TOKEN,    &xTrue,             sizeof( xTrue )                               },
            { CKA_PRIVATE,  &xTrue,             sizeof( xTrue )                               },
            { CKA_SIGN,     &xTrue,             sizeof( xTrue )                               },
            { CKA_LABEL,    pucPrivateKeyLabel, strlen( ( const char * ) pucPrivateKeyLabel ) }
        };

        mbedtls_pk_init_CMockIgnore();
        mbedtls_pk_info_from_type_IgnoreAndReturn( 0 );
        mbedtls_pk_setup_IgnoreAndReturn( -1 );
        vPkcs11Free_Stub( vPkcs11FreeCb );
        mbedtls_free_Stub( vPkcs11FreeCb );
        mbedtls_pk_free_CMockIgnore();
        xResult = C_GenerateKeyPair( xSession, &xMechanism, xPublicKeyTemplate,
                                     sizeof( xPublicKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                                     xPrivateKeyTemplate, sizeof( xPrivateKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                                     &xPubKeyHandle, &xPrivKeyHandle );
        TEST_ASSERT_EQUAL( CKR_FUNCTION_FAILED, xResult );

        mbedtls_pk_setup_IgnoreAndReturn( 0 );
        mbedtls_ecp_gen_key_IgnoreAndReturn( -1 );
        xResult = C_GenerateKeyPair( xSession, &xMechanism, xPublicKeyTemplate,
                                     sizeof( xPublicKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                                     xPrivateKeyTemplate, sizeof( xPrivateKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                                     &xPubKeyHandle, &xPrivKeyHandle );
        TEST_ASSERT_EQUAL( CKR_FUNCTION_FAILED, xResult );

        mbedtls_ecp_gen_key_IgnoreAndReturn( 0 );
        mbedtls_pk_write_pubkey_der_IgnoreAndReturn( 0 );
        xResult = C_GenerateKeyPair( xSession, &xMechanism, xPublicKeyTemplate,
                                     sizeof( xPublicKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                                     xPrivateKeyTemplate, sizeof( xPrivateKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                                     &xPubKeyHandle, &xPrivKeyHandle );
        TEST_ASSERT_EQUAL( CKR_GENERAL_ERROR, xResult );

        mbedtls_pk_write_pubkey_der_IgnoreAndReturn( 1 );
        PKCS11_PAL_SaveObject_IgnoreAndReturn( 1 );
        mbedtls_pk_write_key_der_IgnoreAndReturn( 0 );
        xResult = C_GenerateKeyPair( xSession, &xMechanism, xPublicKeyTemplate,
                                     sizeof( xPublicKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                                     xPrivateKeyTemplate, sizeof( xPrivateKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                                     &xPubKeyHandle, &xPrivKeyHandle );
        TEST_ASSERT_EQUAL( CKR_GENERAL_ERROR, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}

/*!
 * @brief C_GenerateKeyPair ECDSA can't lock semaphore
 *
 */
void test_pkcs11_C_GenerateKeyPairECDSALockFail( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = 0;
    CK_OBJECT_HANDLE xPrivKeyHandle = 0;
    CK_OBJECT_HANDLE xPubKeyHandle = 0;

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        char * pucPublicKeyLabel = pkcs11configLABEL_DEVICE_PUBLIC_KEY_FOR_TLS;
        char * pucPrivateKeyLabel = pkcs11configLABEL_DEVICE_PRIVATE_KEY_FOR_TLS;

        CK_MECHANISM xMechanism =
        {
            CKM_EC_KEY_PAIR_GEN, NULL_PTR, 0
        };
        CK_BYTE xEcParams[] = pkcs11DER_ENCODED_OID_P256; /* prime256v1 */
        CK_KEY_TYPE xKeyType = CKK_EC;

        CK_BBOOL xTrue = CK_TRUE;
        CK_ATTRIBUTE xPublicKeyTemplate[] =
        {
            { CKA_KEY_TYPE,  &xKeyType,         sizeof( xKeyType )                           },
            { CKA_TOKEN,     &xTrue,            sizeof( xTrue )                              },
            { CKA_VERIFY,    &xTrue,            sizeof( xTrue )                              },
            { CKA_EC_PARAMS, xEcParams,         sizeof( xEcParams )                          },
            { CKA_LABEL,     pucPublicKeyLabel, strlen( ( const char * ) pucPublicKeyLabel ) }
        };

        CK_ATTRIBUTE xPrivateKeyTemplate[] =
        {
            { CKA_KEY_TYPE, &xKeyType,          sizeof( xKeyType )                            },
            { CKA_TOKEN,    &xTrue,             sizeof( xTrue )                               },
            { CKA_PRIVATE,  &xTrue,             sizeof( xTrue )                               },
            { CKA_SIGN,     &xTrue,             sizeof( xTrue )                               },
            { CKA_LABEL,    pucPrivateKeyLabel, strlen( ( const char * ) pucPrivateKeyLabel ) }
        };

        mbedtls_pk_init_CMockIgnore();
        mbedtls_pk_info_from_type_IgnoreAndReturn( 0 );
        mbedtls_pk_setup_IgnoreAndReturn( 0 );
        mbedtls_ecp_gen_key_IgnoreAndReturn( 0 );
        mbedtls_pk_write_pubkey_der_IgnoreAndReturn( 1 );
        PKCS11_PAL_SaveObject_IgnoreAndReturn( 1 );
        mbedtls_pk_write_key_der_IgnoreAndReturn( 1 );
        PKCS11_PAL_SaveObject_IgnoreAndReturn( 2 );
        mock_osal_mutex_lock_IgnoreAndReturn( 0 );
        mock_osal_mutex_unlock_IgnoreAndReturn( 0 );
        mock_osal_mutex_lock_IgnoreAndReturn( -1 );
        vPkcs11Free_Stub( vPkcs11FreeCb );
        mbedtls_free_Stub( vPkcs11FreeCb );
        mbedtls_pk_free_CMockIgnore();
        PKCS11_PAL_GetObjectValue_IgnoreAndReturn( CKR_OK );
        PKCS11_PAL_SaveObject_IgnoreAndReturn( 2 );
        PKCS11_PAL_DestroyObject_IgnoreAndReturn( CKR_OK );
        mock_osal_mutex_lock_IgnoreAndReturn( 0 );
        PKCS11_PAL_GetObjectValueCleanup_CMockIgnore();
        xResult = C_GenerateKeyPair( xSession, &xMechanism, xPublicKeyTemplate,
                                     sizeof( xPublicKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                                     xPrivateKeyTemplate, sizeof( xPrivateKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                                     &xPubKeyHandle, &xPrivKeyHandle );
        TEST_ASSERT_EQUAL( CKR_CANT_LOCK, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}

/*!
 * @brief C_GenerateKeyPair ECDSA private key attribute not set to private.
 *
 */
void test_pkcs11_C_GenerateKeyPairECDSABadPrivateKeyParam( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = 0;
    CK_OBJECT_HANDLE xPrivKeyHandle = 0;
    CK_OBJECT_HANDLE xPubKeyHandle = 0;

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        char * pucPublicKeyLabel = pkcs11configLABEL_DEVICE_PUBLIC_KEY_FOR_TLS;
        char * pucPrivateKeyLabel = pkcs11configLABEL_DEVICE_PRIVATE_KEY_FOR_TLS;

        CK_MECHANISM xMechanism =
        {
            CKM_EC_KEY_PAIR_GEN, NULL_PTR, 0
        };
        CK_BYTE xEcParams[] = pkcs11DER_ENCODED_OID_P256; /* prime256v1 */
        CK_KEY_TYPE xKeyType = CKK_EC;

        CK_BBOOL xTrue = CK_TRUE;
        CK_BBOOL xFalse = CK_FALSE;
        CK_ATTRIBUTE xPublicKeyTemplate[] =
        {
            { CKA_KEY_TYPE,  &xKeyType,         sizeof( xKeyType )                           },
            { CKA_VERIFY,    &xTrue,            sizeof( xTrue )                              },
            { CKA_EC_PARAMS, xEcParams,         sizeof( xEcParams )                          },
            { CKA_LABEL,     pucPublicKeyLabel, strlen( ( const char * ) pucPublicKeyLabel ) }
        };

        CK_ATTRIBUTE xPrivateKeyTemplate[] =
        {
            { CKA_KEY_TYPE, &xKeyType,          sizeof( xKeyType )                            },
            { CKA_TOKEN,    &xTrue,             sizeof( xTrue )                               },
            { CKA_PRIVATE,  &xFalse,            sizeof( xFalse )                              },
            { CKA_SIGN,     &xTrue,             sizeof( xTrue )                               },
            { CKA_LABEL,    pucPrivateKeyLabel, strlen( ( const char * ) pucPrivateKeyLabel ) }
        };

        mbedtls_pk_init_CMockIgnore();
        mbedtls_pk_info_from_type_IgnoreAndReturn( 0 );
        mbedtls_pk_setup_IgnoreAndReturn( 0 );
        mbedtls_ecp_gen_key_IgnoreAndReturn( 0 );
        mbedtls_pk_write_pubkey_der_IgnoreAndReturn( 1 );
        PKCS11_PAL_SaveObject_IgnoreAndReturn( 1 );
        mbedtls_pk_write_key_der_IgnoreAndReturn( 1 );
        PKCS11_PAL_SaveObject_IgnoreAndReturn( 2 );
        vPkcs11Free_Stub( vPkcs11FreeCb );
        mbedtls_free_Stub( vPkcs11FreeCb );
        mbedtls_pk_free_CMockIgnore();
        xResult = C_GenerateKeyPair( xSession, &xMechanism, xPublicKeyTemplate,
                                     sizeof( xPublicKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                                     xPrivateKeyTemplate, sizeof( xPrivateKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                                     &xPubKeyHandle, &xPrivKeyHandle );
        TEST_ASSERT_EQUAL( CKR_TEMPLATE_INCONSISTENT, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}

/*!
 * @brief C_GenerateKeyPair Calloc Fail
 *
 */
void test_pkcs11_C_GenerateKeyPairCallocFails( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = 0;
    CK_OBJECT_HANDLE xPrivKeyHandle = 0;
    CK_OBJECT_HANDLE xPubKeyHandle = 0;

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        char * pucPublicKeyLabel = pkcs11configLABEL_DEVICE_PUBLIC_KEY_FOR_TLS;
        char * pucPrivateKeyLabel = pkcs11configLABEL_DEVICE_PRIVATE_KEY_FOR_TLS;

        CK_MECHANISM xMechanism =
        {
            CKM_EC_KEY_PAIR_GEN, NULL_PTR, 0
        };
        CK_BYTE xEcParams[] = pkcs11DER_ENCODED_OID_P256; /* prime256v1 */
        CK_KEY_TYPE xKeyType = CKK_EC;

        CK_BBOOL xTrue = CK_TRUE;
        CK_BBOOL xFalse = CK_FALSE;
        CK_ATTRIBUTE xPublicKeyTemplate[] =
        {
            { CKA_KEY_TYPE,  &xKeyType,         sizeof( xKeyType )                           },
            { CKA_VERIFY,    &xTrue,            sizeof( xTrue )                              },
            { CKA_EC_PARAMS, xEcParams,         sizeof( xEcParams )                          },
            { CKA_LABEL,     pucPublicKeyLabel, strlen( ( const char * ) pucPublicKeyLabel ) }
        };

        CK_ATTRIBUTE xPrivateKeyTemplate[] =
        {
            { CKA_KEY_TYPE, &xKeyType,          sizeof( xKeyType )                            },
            { CKA_TOKEN,    &xTrue,             sizeof( xTrue )                               },
            { CKA_PRIVATE,  &xFalse,            sizeof( xFalse )                              },
            { CKA_SIGN,     &xTrue,             sizeof( xTrue )                               },
            { CKA_LABEL,    pucPrivateKeyLabel, strlen( ( const char * ) pucPrivateKeyLabel ) }
        };

        mbedtls_calloc_IgnoreAndReturn( NULL );
        mbedtls_free_CMockIgnore();

        mbedtls_pk_free_CMockIgnore();
        xResult = C_GenerateKeyPair( xSession, &xMechanism, xPublicKeyTemplate,
                                     sizeof( xPublicKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                                     xPrivateKeyTemplate, sizeof( xPrivateKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                                     &xPubKeyHandle, &xPrivKeyHandle );
        TEST_ASSERT_EQUAL( CKR_HOST_MEMORY, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}

/*!
 * @brief C_GenerateKeyPair RSA Key Gen
 * @note we will need to update this if we start supporting RSA keygen.
 *
 */
void test_pkcs11_C_GenerateKeyPairRSAGen( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = 0;
    CK_OBJECT_HANDLE xPrivKeyHandle = 0;
    CK_OBJECT_HANDLE xPubKeyHandle = 0;

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        char * pucPublicKeyLabel = pkcs11configLABEL_DEVICE_PUBLIC_KEY_FOR_TLS;
        char * pucPrivateKeyLabel = pkcs11configLABEL_DEVICE_PRIVATE_KEY_FOR_TLS;

        CK_MECHANISM xMechanism =
        {
            CKM_RSA_PKCS_KEY_PAIR_GEN, NULL_PTR, 0
        };
        CK_BYTE xEcParams[] = pkcs11DER_ENCODED_OID_P256; /* prime256v1 */
        CK_KEY_TYPE xKeyType = CKK_RSA;

        CK_BBOOL xTrue = CK_TRUE;
        CK_BBOOL xFalse = CK_FALSE;
        CK_ATTRIBUTE xPublicKeyTemplate[] =
        {
            { CKA_KEY_TYPE, &xKeyType,         sizeof( xKeyType )                           },
            { CKA_VERIFY,   &xTrue,            sizeof( xTrue )                              },
            { CKA_LABEL,    pucPublicKeyLabel, strlen( ( const char * ) pucPublicKeyLabel ) }
        };

        CK_ATTRIBUTE xPrivateKeyTemplate[] =
        {
            { CKA_KEY_TYPE, &xKeyType,          sizeof( xKeyType )                            },
            { CKA_TOKEN,    &xTrue,             sizeof( xTrue )                               },
            { CKA_PRIVATE,  &xFalse,            sizeof( xFalse )                              },
            { CKA_SIGN,     &xTrue,             sizeof( xTrue )                               },
            { CKA_LABEL,    pucPrivateKeyLabel, strlen( ( const char * ) pucPrivateKeyLabel ) }
        };

        mbedtls_calloc_IgnoreAndReturn( &xMechanism );
        mbedtls_free_CMockIgnore();
        mbedtls_pk_free_CMockIgnore();
        xResult = C_GenerateKeyPair( xSession, &xMechanism, xPublicKeyTemplate,
                                     sizeof( xPublicKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                                     xPrivateKeyTemplate, sizeof( xPrivateKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                                     &xPubKeyHandle, &xPrivKeyHandle );
        TEST_ASSERT_EQUAL( CKR_MECHANISM_INVALID, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}

/*!
 * @brief C_GenerateKeyPair Bad Args.
 *
 */
void test_pkcs11_C_GenerateKeyPairBadArgs( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = 0;
    CK_OBJECT_HANDLE xPrivKeyHandle = 0;
    CK_OBJECT_HANDLE xPubKeyHandle = 0;

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        char * pucPublicKeyLabel = pkcs11configLABEL_DEVICE_PUBLIC_KEY_FOR_TLS;
        char * pucPrivateKeyLabel = pkcs11configLABEL_DEVICE_PRIVATE_KEY_FOR_TLS;

        CK_MECHANISM xMechanism =
        {
            CKM_EC_KEY_PAIR_GEN, NULL_PTR, 0
        };
        CK_BYTE xEcParams[] = pkcs11DER_ENCODED_OID_P256;
        CK_BYTE xEcGarbageParams[ sizeof( xEcParams ) ] = { 0xAA };
        CK_KEY_TYPE xKeyType = CKK_EC;
        CK_KEY_TYPE xBadKeyType = CKK_RSA;

        CK_BBOOL xTrue = CK_TRUE;
        CK_BBOOL xFalse = CK_FALSE;
        CK_ATTRIBUTE xPublicKeyTemplate[] =
        {
            { CKA_KEY_TYPE,  &xKeyType,         sizeof( xKeyType )                           },
            { CKA_VERIFY,    &xTrue,            sizeof( xTrue )                              },
            { CKA_EC_PARAMS, xEcParams,         sizeof( xEcParams )                          },
            { CKA_LABEL,     pucPublicKeyLabel, strlen( ( const char * ) pucPublicKeyLabel ) },
            { CKA_TOKEN,     &xTrue,            sizeof( xTrue )                              }
        };

        CK_ATTRIBUTE xPrivateKeyTemplate[] =
        {
            { CKA_KEY_TYPE, &xKeyType,          sizeof( xKeyType )                            },
            { CKA_TOKEN,    &xTrue,             sizeof( xTrue )                               },
            { CKA_PRIVATE,  &xTrue,             sizeof( xTrue )                               },
            { CKA_SIGN,     &xTrue,             sizeof( xTrue )                               },
            { CKA_LABEL,    pucPrivateKeyLabel, strlen( ( const char * ) pucPrivateKeyLabel ) }
        };

        mbedtls_calloc_Stub( pvPkcs11CallocCb );
        vPkcs11Free_Stub( vPkcs11FreeCb );
        mbedtls_free_Stub( vPkcs11FreeCb );
        mbedtls_pk_free_CMockIgnore();
        xPrivateKeyTemplate[ 0 ].pValue = &xBadKeyType;
        xResult = C_GenerateKeyPair( xSession, &xMechanism, xPublicKeyTemplate,
                                     sizeof( xPublicKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                                     xPrivateKeyTemplate, sizeof( xPrivateKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                                     &xPubKeyHandle, &xPrivKeyHandle );
        TEST_ASSERT_EQUAL( CKR_TEMPLATE_INCONSISTENT, xResult );
        xPrivateKeyTemplate[ 0 ].pValue = &xKeyType;

        xPublicKeyTemplate[ 2 ].pValue = &xEcGarbageParams;
        xResult = C_GenerateKeyPair( xSession, &xMechanism, xPublicKeyTemplate,
                                     sizeof( xPublicKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                                     xPrivateKeyTemplate, sizeof( xPrivateKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                                     &xPubKeyHandle, &xPrivKeyHandle );
        TEST_ASSERT_EQUAL( CKR_TEMPLATE_INCONSISTENT, xResult );
        xPublicKeyTemplate[ 2 ].pValue = &xEcParams;

        xResult = C_GenerateKeyPair( xSession, &xMechanism, xPublicKeyTemplate,
                                     sizeof( xPublicKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                                     xPrivateKeyTemplate,
                                     ( sizeof( xPrivateKeyTemplate ) / sizeof( CK_ATTRIBUTE ) ) - 1,
                                     &xPubKeyHandle, &xPrivKeyHandle );
        TEST_ASSERT_EQUAL( CKR_TEMPLATE_INCOMPLETE, xResult );

        xResult = C_GenerateKeyPair( xSession, &xMechanism, xPublicKeyTemplate,
                                     sizeof( xPublicKeyTemplate ) / sizeof( CK_ATTRIBUTE ) - 3,
                                     xPrivateKeyTemplate,
                                     ( sizeof( xPrivateKeyTemplate ) / sizeof( CK_ATTRIBUTE ) ),
                                     &xPubKeyHandle, &xPrivKeyHandle );
        TEST_ASSERT_EQUAL( CKR_TEMPLATE_INCOMPLETE, xResult );

        xPrivateKeyTemplate[ 3 ].pValue = &xFalse;
        xResult = C_GenerateKeyPair( xSession, &xMechanism, xPublicKeyTemplate,
                                     sizeof( xPublicKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                                     xPrivateKeyTemplate, sizeof( xPrivateKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                                     &xPubKeyHandle, &xPrivKeyHandle );
        TEST_ASSERT_EQUAL( CKR_TEMPLATE_INCONSISTENT, xResult );
        xPrivateKeyTemplate[ 3 ].pValue = &xTrue;

        xPrivateKeyTemplate[ 1 ].pValue = &xFalse;
        xResult = C_GenerateKeyPair( xSession, &xMechanism, xPublicKeyTemplate,
                                     sizeof( xPublicKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                                     xPrivateKeyTemplate, sizeof( xPrivateKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                                     &xPubKeyHandle, &xPrivKeyHandle );
        TEST_ASSERT_EQUAL( CKR_TEMPLATE_INCONSISTENT, xResult );
        xPrivateKeyTemplate[ 1 ].pValue = &xTrue;

        xPublicKeyTemplate[ 1 ].pValue = &xFalse;
        xResult = C_GenerateKeyPair( xSession, &xMechanism, xPublicKeyTemplate,
                                     sizeof( xPublicKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                                     xPrivateKeyTemplate, sizeof( xPrivateKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                                     &xPubKeyHandle, &xPrivKeyHandle );
        TEST_ASSERT_EQUAL( CKR_TEMPLATE_INCONSISTENT, xResult );
        xPublicKeyTemplate[ 1 ].pValue = &xTrue;

        xPublicKeyTemplate[ 0 ].pValue = &xBadKeyType;
        xResult = C_GenerateKeyPair( xSession, &xMechanism, xPublicKeyTemplate,
                                     sizeof( xPublicKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                                     xPrivateKeyTemplate, sizeof( xPrivateKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                                     &xPubKeyHandle, &xPrivKeyHandle );
        TEST_ASSERT_EQUAL( CKR_TEMPLATE_INCONSISTENT, xResult );
        xPublicKeyTemplate[ 0 ].pValue = &xKeyType;

        xPublicKeyTemplate[ 4 ].pValue = &xFalse;
        xResult = C_GenerateKeyPair( xSession, &xMechanism, xPublicKeyTemplate,
                                     sizeof( xPublicKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                                     xPrivateKeyTemplate, sizeof( xPrivateKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                                     &xPubKeyHandle, &xPrivKeyHandle );
        TEST_ASSERT_EQUAL( CKR_TEMPLATE_INCONSISTENT, xResult );
        xPublicKeyTemplate[ 4 ].pValue = &xTrue;

        xResult = C_GenerateKeyPair( xSession, &xMechanism, xPublicKeyTemplate,
                                     sizeof( xPublicKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                                     NULL, sizeof( xPrivateKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                                     &xPubKeyHandle, &xPrivKeyHandle );
        TEST_ASSERT_EQUAL( CKR_ARGUMENTS_BAD, xResult );

        xPrivateKeyTemplate[ 0 ].type = CKA_LABEL + CKA_KEY_TYPE + CKA_SIGN + CKA_PRIVATE + CKA_TOKEN;
        xResult = C_GenerateKeyPair( xSession, &xMechanism, xPublicKeyTemplate,
                                     sizeof( xPublicKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                                     xPrivateKeyTemplate, sizeof( xPrivateKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                                     &xPubKeyHandle, &xPrivKeyHandle );
        TEST_ASSERT_EQUAL( CKR_ATTRIBUTE_TYPE_INVALID, xResult );

        xPrivateKeyTemplate[ 0 ].type = CKA_KEY_TYPE;
        xPublicKeyTemplate[ 0 ].type = CKA_LABEL + CKA_KEY_TYPE + CKA_EC_PARAMS + CKA_VERIFY + CKA_TOKEN;
        xResult = C_GenerateKeyPair( xSession, &xMechanism, xPublicKeyTemplate,
                                     sizeof( xPublicKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                                     xPrivateKeyTemplate, sizeof( xPrivateKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                                     &xPubKeyHandle, &xPrivKeyHandle );
        TEST_ASSERT_EQUAL( CKR_TEMPLATE_INCONSISTENT, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}
/* ======================  TESTING C_GenerateRandom  ============================ */

/*!
 * @brief C_GenerateRandom happy path.
 *
 */
void test_pkcs11_C_GenerateRandom( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = 0;
    CK_BYTE ucRandData[ 3 ] = { 0 };
    CK_ULONG ulRandLen = sizeof( ucRandData );

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        mbedtls_ctr_drbg_random_IgnoreAndReturn( 0 );
        xResult = C_GenerateRandom( xSession, ucRandData, ulRandLen );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}

/*!
 * @brief C_GenerateRandom drbg failed.
 *
 */
void test_pkcs11_C_GenerateRandomDrbgFail( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = 0;
    CK_BYTE ucRandData[ 3 ] = { 0 };
    CK_ULONG ulRandLen = sizeof( ucRandData );

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        mbedtls_ctr_drbg_random_IgnoreAndReturn( -1 );
        xResult = C_GenerateRandom( xSession, ucRandData, ulRandLen );
        TEST_ASSERT_EQUAL( CKR_FUNCTION_FAILED, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}

/*!
 * @brief C_GenerateRandom drbg session was not initialized.
 *
 */
void test_pkcs11_C_GenerateRandomDrbgSessionInvalid( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = 0;
    CK_BYTE ucRandData[ 3 ] = { 0 };
    CK_ULONG ulRandLen = sizeof( ucRandData );

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        mbedtls_entropy_free_CMockIgnore();
        mbedtls_ctr_drbg_free_CMockIgnore();
        mock_osal_mutex_free_CMockIgnore();
        xResult = C_Finalize( NULL );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        mbedtls_ctr_drbg_random_IgnoreAndReturn( ulRandLen );
        xResult = C_GenerateRandom( xSession, ucRandData, ulRandLen );
        TEST_ASSERT_EQUAL( CKR_CRYPTOKI_NOT_INITIALIZED, xResult );
    }
}

/*!
 * @brief C_GenerateRandom bad args.
 *
 */
void test_pkcs11_C_GenerateRandomBadArgs( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = 0;

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        xResult = C_GenerateRandom( xSession, NULL, 0 );
        TEST_ASSERT_EQUAL( CKR_ARGUMENTS_BAD, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}

/* ======================  TESTING C_DestroyObject  ============================ */

/*!
 * @brief C_DestroyObject happy path.
 *
 */
void test_pkcs11_C_DestroyObject( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = 0;
    CK_OBJECT_HANDLE xObject = 0;

    if( TEST_PROTECT() )
    {
        prvCommonInitStubs( &xSession );

        xResult = prvCreateEcPub( &xSession, &xObject );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        xResult = prvCreateEcPriv( &xSession, &xObject );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        PKCS11_PAL_GetObjectValue_IgnoreAndReturn( CKR_OK );
        mbedtls_calloc_Stub( pvPkcs11CallocCb );
        vPkcs11Free_Stub( vPkcs11FreeCb );
        mbedtls_free_Stub( vPkcs11FreeCb );
        PKCS11_PAL_SaveObject_IgnoreAndReturn( 2 );
        PKCS11_PAL_GetObjectValueCleanup_CMockIgnore();
        PKCS11_PAL_DestroyObject_IgnoreAndReturn( CKR_OK );
        xResult = C_DestroyObject( xSession, xObject );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}

/*!
 * @brief C_DestroyObject failed to get mutex when removing object from internal list.
 *
 */
void test_pkcs11_C_DestroyObjectNoLock( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = 0;
    CK_OBJECT_HANDLE xObject = 0;

    if( TEST_PROTECT() )
    {
        prvCommonInitStubs( &xSession );

        xResult = prvCreateEcPub( &xSession, &xObject );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        xResult = prvCreateEcPriv( &xSession, &xObject );
        TEST_ASSERT_EQUAL( CKR_OK, xResult );

        PKCS11_PAL_GetObjectValue_IgnoreAndReturn( CKR_OK );
        mbedtls_calloc_Stub( pvPkcs11CallocCb );
        vPkcs11Free_Stub( vPkcs11FreeCb );
        mbedtls_free_Stub( vPkcs11FreeCb );
        PKCS11_PAL_SaveObject_IgnoreAndReturn( 2 );
        PKCS11_PAL_GetObjectValueCleanup_CMockIgnore();
        PKCS11_PAL_DestroyObject_IgnoreAndReturn( CKR_OK );
        mock_osal_mutex_lock_ExpectAnyArgsAndReturn( -1 );
        xResult = C_DestroyObject( xSession, xObject );
        TEST_ASSERT_EQUAL( CKR_CANT_LOCK, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}

/*!
 * @brief C_DestroyObject invalid object is passed to C_DestroyObject, and it can't be found.
 *
 */
void test_pkcs11_C_DestroyObjectNullLabel( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = 0;
    CK_OBJECT_HANDLE xObject = 1;

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        PKCS11_PAL_GetObjectValue_IgnoreAndReturn( CKR_OK );
        mbedtls_calloc_Stub( pvPkcs11CallocCb );
        vPkcs11Free_Stub( vPkcs11FreeCb );
        mbedtls_free_Stub( vPkcs11FreeCb );
        xResult = C_DestroyObject( xSession, xObject );
        TEST_ASSERT_EQUAL( CKR_OBJECT_HANDLE_INVALID, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}

/*!
 * @brief C_DestroyObject invalid object handle is passed to C_DestroyObject
 *
 */
void test_pkcs11_C_DestroyObjectBadHandle( void )
{
    CK_RV xResult = CKR_OK;
    CK_SESSION_HANDLE xSession = 0;
    CK_OBJECT_HANDLE xObject = ( CK_OBJECT_HANDLE ) -1;

    prvCommonInitStubs( &xSession );

    if( TEST_PROTECT() )
    {
        xResult = C_DestroyObject( xSession, xObject );
        TEST_ASSERT_EQUAL( CKR_OBJECT_HANDLE_INVALID, xResult );
    }

    if( TEST_PROTECT() )
    {
        prvCommonDeinitStubs( &xSession );
    }
}
