/*
 * AWS IoT Device SDK for Embedded C 202108.00
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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

/* Standard includes. */
#include <assert.h>
#include <stdlib.h>
#include <string.h>

/* POSIX includes. */
#include <unistd.h>

/* Include Demo Config as the first non-system header. */
#include "demo_config.h"

/* Common HTTP demo utilities. */
#include "http_demo_utils.h"

/* HTTP API header. */
#include "core_http_client.h"

/* Transport interface implementation include header for TLS. */
#include "network_transport.h"
       
#ifdef CONFIG_EXAMPLE_USE_ESP_SECURE_CERT_MGR
    #include "esp_secure_cert_read.h"    
#endif

extern const char root_cert_auth_start[] asm("_binary_root_cert_auth_crt_start");
extern const char root_cert_auth_end[]   asm("_binary_root_cert_auth_crt_end");

/* Check that a path for the client certificate is defined. */
#ifndef CONFIG_EXAMPLE_USE_ESP_SECURE_CERT_MGR
    extern const char client_cert_start[] asm("_binary_client_crt_start");
    extern const char client_cert_end[] asm("_binary_client_crt_end");
    extern const char client_key_start[] asm("_binary_client_key_start");
    extern const char client_key_end[] asm("_binary_client_key_end");
#endif

/**
 * @brief ALPN protocol name to be sent as part of the ClientHello message.
 *
 * @note When using ALPN, port 443 must be used to connect to AWS IoT Core.
 */
#define IOT_CORE_ALPN_PROTOCOL_NAME    "x-amzn-http-ca"

/* Check that transport timeout for transport send and receive is defined. */
#ifndef TRANSPORT_SEND_RECV_TIMEOUT_MS
    #define TRANSPORT_SEND_RECV_TIMEOUT_MS    ( 1500 )
#endif

/* Check that size of the user buffer is defined. */
#ifndef USER_BUFFER_LENGTH
    #define USER_BUFFER_LENGTH    ( 2048 )
#endif

/* Check that a request body to send for the POST request is defined. */
#ifndef REQUEST_BODY
    #error "Please define a REQUEST_BODY."
#endif

/**
 * @brief The length of the AWS IoT Endpoint.
 */
#define AWS_IOT_ENDPOINT_LENGTH    ( sizeof( AWS_IOT_ENDPOINT ) - 1 )

/**
 * @brief The length of the HTTP POST method.
 */
#define HTTP_METHOD_POST_LENGTH    ( sizeof( HTTP_METHOD_POST ) - 1 )

/**
 * @brief The length of the HTTP POST path.
 */
#define POST_PATH_LENGTH           ( sizeof( POST_PATH ) - 1 )

/**
 * @brief Length of the request body.
 */
#define REQUEST_BODY_LENGTH        ( sizeof( REQUEST_BODY ) - 1 )

/**
 * @brief A buffer used in the demo for storing HTTP request headers and
 * HTTP response headers and body.
 *
 * @note This demo shows how the same buffer can be re-used for storing the HTTP
 * response after the HTTP request is sent out. However, the user can also
 * decide to use separate buffers for storing the HTTP request and response.
 */
static uint8_t userBuffer[ USER_BUFFER_LENGTH ];

/**
 * @brief Static buffer for TLS Context Semaphore.
 */
static StaticSemaphore_t xTlsContextSemaphoreBuffer;

/*-----------------------------------------------------------*/

int aws_iot_demo_main( int argc, char ** argv );

/**
 * @brief Connect to HTTP server with reconnection retries.
 *
 * @param[out] pNetworkContext The output parameter to return the created network context.
 *
 * @return EXIT_FAILURE on failure; EXIT_SUCCESS on successful connection.
 */
static int32_t connectToServer( NetworkContext_t * pNetworkContext );

/**
 * @brief Send an HTTP request based on a specified method and path, then
 * print the response received from the server.
 *
 * @param[in] pTransportInterface The transport interface for making network calls.
 * @param[in] pMethod The HTTP request method.
 * @param[in] methodLen The length of the HTTP request method.
 * @param[in] pPath The Request-URI to the objects of interest.
 * @param[in] pathLen The length of the Request-URI.
 *
 * @return EXIT_FAILURE on failure; EXIT_SUCCESS on success.
 */
static int32_t sendHttpRequest( const TransportInterface_t * pTransportInterface,
                                const char * pMethod,
                                size_t methodLen,
                                const char * pPath,
                                size_t pathLen );

/*-----------------------------------------------------------*/

static int32_t connectToServer( NetworkContext_t * pNetworkContext )
{
    int32_t returnStatus = EXIT_FAILURE;

    /* Status returned by transport implementation. */
    TlsTransportStatus_t tlsStatus;

    /* Initialize TLS credentials. */
    pNetworkContext->pcHostname = AWS_IOT_ENDPOINT;
    pNetworkContext->xPort = AWS_HTTPS_PORT;
    pNetworkContext->pxTls = NULL;
    pNetworkContext->xTlsContextSemaphore = xSemaphoreCreateMutexStatic(&xTlsContextSemaphoreBuffer);

#ifdef CONFIG_EXAMPLE_USE_SECURE_ELEMENT
    pNetworkContext->use_secure_element = true;

#elif defined(CONFIG_EXAMPLE_USE_ESP_SECURE_CERT_MGR)
    if (esp_secure_cert_get_device_cert(&pNetworkContext->pcClientCert, &pNetworkContext->pcClientCertSize) != ESP_OK) {
        LogError( ( "Failed to obtain flash address of device cert") );
        return EXIT_FAILURE;
    }
#ifdef CONFIG_ESP_SECURE_CERT_DS_PERIPHERAL
    pNetworkContext->ds_data = esp_secure_cert_get_ds_ctx();
    if (pNetworkContext->ds_data == NULL) {
        LogError( ( "Failed to obtain the ds context") );
        return EXIT_FAILURE;
    }
#else /* !CONFIG_ESP_SECURE_CERT_DS_PERIPHERAL */
    if (esp_secure_cert_get_priv_key(&pNetworkContext->pcClientKey, &pNetworkContext->pcClientKeySize) != ESP_OK) {
        LogError( ( "Failed to obtain flash address of private_key") );
        return EXIT_FAILURE;
    }
#endif /* CONFIG_ESP_SECURE_CERT_DS_PERIPHERAL */
#else /* !CONFIG_EXAMPLE_USE_SECURE_ELEMENT && !CONFIG_EXAMPLE_USE_ESP_SECURE_CERT_MGR  */
    pNetworkContext->pcClientCert = client_cert_start;
    pNetworkContext->pcClientCertSize = client_cert_end - client_cert_start;
    pNetworkContext->pcClientKey = client_key_start;
    pNetworkContext->pcClientKeySize = client_key_end - client_key_start;
#endif /* CONFIG_EXAMPLE_USE_SECURE_ELEMENT */

    pNetworkContext->pcServerRootCA = root_cert_auth_start;
    pNetworkContext->pcServerRootCASize = root_cert_auth_end - root_cert_auth_start;

    pNetworkContext->disableSni = 0;

    /* ALPN is required when communicating to AWS IoT Core over port 443 through HTTP. */
    if( AWS_HTTPS_PORT == 443 )
    {
        static const char * pcAlpnProtocols[] = { NULL, NULL };
        pcAlpnProtocols[0] = IOT_CORE_ALPN_PROTOCOL_NAME;
        pNetworkContext->pAlpnProtos = pcAlpnProtocols;

    } else {
         pNetworkContext->pAlpnProtos = NULL;
    }

    /* Establish a TLS session with the HTTP server. This example connects
     * to the HTTP server as specified in AWS_IOT_ENDPOINT and AWS_HTTPS_PORT
     * in demo_config.h. */
    LogInfo( ( "Establishing a TLS session to %.*s:%d.",
               ( int ) AWS_IOT_ENDPOINT_LENGTH,
               AWS_IOT_ENDPOINT,
               AWS_HTTPS_PORT ) );
    tlsStatus = xTlsConnect ( pNetworkContext );

    if( tlsStatus == TLS_TRANSPORT_SUCCESS )
    {
        returnStatus = EXIT_SUCCESS;
    }
    else
    {
        returnStatus = EXIT_FAILURE;
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

static int32_t sendHttpRequest( const TransportInterface_t * pTransportInterface,
                                const char * pMethod,
                                size_t methodLen,
                                const char * pPath,
                                size_t pathLen )
{
    /* Return value of this method. */
    int32_t returnStatus = EXIT_SUCCESS;

    /* Configurations of the initial request headers that are passed to
     * #HTTPClient_InitializeRequestHeaders. */
    HTTPRequestInfo_t requestInfo;
    /* Represents a response returned from an HTTP server. */
    HTTPResponse_t response;
    /* Represents header data that will be sent in an HTTP request. */
    HTTPRequestHeaders_t requestHeaders;

    /* Return value of all methods from the HTTP Client library API. */
    HTTPStatus_t httpStatus = HTTPSuccess;

    assert( pMethod != NULL );
    assert( pPath != NULL );

    /* Initialize all HTTP Client library API structs to 0. */
    ( void ) memset( &requestInfo, 0, sizeof( requestInfo ) );
    ( void ) memset( &response, 0, sizeof( response ) );
    ( void ) memset( &requestHeaders, 0, sizeof( requestHeaders ) );

    /* Initialize the request object. */
    requestInfo.pHost = AWS_IOT_ENDPOINT;
    requestInfo.hostLen = AWS_IOT_ENDPOINT_LENGTH;
    requestInfo.pMethod = pMethod;
    requestInfo.methodLen = methodLen;
    requestInfo.pPath = pPath;
    requestInfo.pathLen = pathLen;

    /* Set "Connection" HTTP header to "keep-alive" so that multiple requests
     * can be sent over the same established TCP connection. */
    requestInfo.reqFlags = HTTP_REQUEST_KEEP_ALIVE_FLAG;

    /* Set the buffer used for storing request headers. */
    requestHeaders.pBuffer = userBuffer;
    requestHeaders.bufferLen = USER_BUFFER_LENGTH;

    httpStatus = HTTPClient_InitializeRequestHeaders( &requestHeaders,
                                                      &requestInfo );

    if( httpStatus == HTTPSuccess )
    {
        /* Initialize the response object. The same buffer used for storing
         * request headers is reused here. */
        response.pBuffer = userBuffer;
        response.bufferLen = USER_BUFFER_LENGTH;

        LogInfo( ( "Sending HTTP %.*s request to %.*s%.*s...",
                   ( int ) requestInfo.methodLen, requestInfo.pMethod,
                   ( int ) AWS_IOT_ENDPOINT_LENGTH, AWS_IOT_ENDPOINT,
                   ( int ) requestInfo.pathLen, requestInfo.pPath ) );
        LogDebug( ( "Request Headers:\n%.*s\n"
                    "Request Body:\n%.*s\n",
                    ( int ) requestHeaders.headersLen,
                    ( char * ) requestHeaders.pBuffer,
                    ( int ) REQUEST_BODY_LENGTH, REQUEST_BODY ) );

        /* Send the request and receive the response. */
        httpStatus = HTTPClient_Send( pTransportInterface,
                                      &requestHeaders,
                                      ( uint8_t * ) REQUEST_BODY,
                                      REQUEST_BODY_LENGTH,
                                      &response,
                                      0 );
    }
    else
    {
        LogError( ( "Failed to initialize HTTP request headers: Error=%s.",
                    HTTPClient_strerror( httpStatus ) ) );
    }

    if( httpStatus == HTTPSuccess )
    {
        LogInfo( ( "Received HTTP response from %.*s%.*s...\n"
                   "Response Headers:\n%.*s\n"
                   "Response Status:\n%u\n"
                   "Response Body:\n%.*s\n",
                   ( int ) AWS_IOT_ENDPOINT_LENGTH, AWS_IOT_ENDPOINT,
                   ( int ) requestInfo.pathLen, requestInfo.pPath,
                   ( int ) response.headersLen, response.pHeaders,
                   response.statusCode,
                   ( int ) response.bodyLen, response.pBody ) );
    }
    else
    {
        LogError( ( "Failed to send HTTP %.*s request to %.*s%.*s: Error=%s.",
                    ( int ) requestInfo.methodLen, requestInfo.pMethod,
                    ( int ) AWS_IOT_ENDPOINT_LENGTH, AWS_IOT_ENDPOINT,
                    ( int ) requestInfo.pathLen, requestInfo.pPath,
                    HTTPClient_strerror( httpStatus ) ) );
    }

    if( httpStatus != HTTPSuccess )
    {
        returnStatus = EXIT_FAILURE;
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

static void cleanupESPSecureMgrCerts( NetworkContext_t * pNetworkContext )
{
#ifdef CONFIG_EXAMPLE_USE_SECURE_ELEMENT
    /* Nothing to be freed */
#elif defined(CONFIG_EXAMPLE_USE_ESP_SECURE_CERT_MGR)
    esp_secure_cert_free_device_cert(&pNetworkContext->pcClientCert);
#ifdef CONFIG_ESP_SECURE_CERT_DS_PERIPHERAL
    esp_secure_cert_free_ds_ctx(pNetworkContext->ds_data);
#else /* !CONFIG_ESP_SECURE_CERT_DS_PERIPHERAL */
    esp_secure_cert_free_priv_key(&pNetworkContext->pcClientKey);
#endif /* CONFIG_ESP_SECURE_CERT_DS_PERIPHERAL */

#else /* !CONFIG_EXAMPLE_USE_SECURE_ELEMENT && !CONFIG_EXAMPLE_USE_ESP_SECURE_CERT_MGR  */
    /* Nothing to be freed */
#endif
    return;
}

/*-----------------------------------------------------------*/

/**
 * @brief Entry point of demo.
 *
 * This example resolves the AWS IoT Core endpoint, establishes a TCP connection,
 * performs a mutually authenticated TLS handshake occurs such that all further
 * communication is encrypted. After which, HTTP Client Library API is used to
 * make a POST request to AWS IoT Core in order to publish a message to a topic
 * named topic with QoS=1 so that all clients subscribed to the topic receive
 * the message at least once. Any possible errors are also logged.
 *
 * @note This example is single-threaded and uses statically allocated memory.
 *
 */
int aws_iot_demo_main( int argc,
          char ** argv )
{
    /* Return value of main. */
    int32_t returnStatus = EXIT_SUCCESS;
    /* The transport layer interface used by the HTTP Client library. */
    TransportInterface_t transportInterface;
    /* The network context for the transport layer interface. */
    NetworkContext_t networkContext = {0};

    ( void ) argc;
    ( void ) argv;

    /* Set the pParams member of the network context with desired transport. */

    /**************************** Connect. ******************************/

    /* Establish TLS connection on top of TCP connection using OpenSSL. */
    if( returnStatus == EXIT_SUCCESS )
    {
        LogInfo( ( "Performing TLS handshake on top of the TCP connection." ) );

        /* Attempt to connect to the HTTP server. If connection fails, retry after
         * a timeout. Timeout value will be exponentially increased till the maximum
         * attempts are reached or maximum timeout value is reached. The function
         * returns EXIT_FAILURE if the TCP connection cannot be established to
         * broker after configured number of attempts. */
        returnStatus = connectToServerWithBackoffRetries( connectToServer,
                                                          &networkContext );

        if( returnStatus == EXIT_FAILURE )
        {
            /* Log error to indicate connection failure after all
             * reconnect attempts are over. */
            LogError( ( "Failed to connect to HTTP server %.*s.",
                        ( int ) AWS_IOT_ENDPOINT_LENGTH,
                        AWS_IOT_ENDPOINT ) );
        }
    }

    /* Define the transport interface. */
    if( returnStatus == EXIT_SUCCESS )
    {
        ( void ) memset( &transportInterface, 0, sizeof( transportInterface ) );
        transportInterface.recv = espTlsTransportRecv;
        transportInterface.send = espTlsTransportSend;
        transportInterface.pNetworkContext = &networkContext;
        transportInterface.writev = NULL;
    }

    /*********************** Send HTTPS request. ************************/

    if( returnStatus == EXIT_SUCCESS )
    {
        returnStatus = sendHttpRequest( &transportInterface,
                                        HTTP_METHOD_POST,
                                        HTTP_METHOD_POST_LENGTH,
                                        POST_PATH,
                                        POST_PATH_LENGTH );
    }

    if( returnStatus == EXIT_SUCCESS )
    {
        /* Log message indicating an iteration completed successfully. */
        LogInfo( ( "Demo completed successfully." ) );
    }

    /************************** Disconnect. *****************************/

    /* End TLS session, then close TCP connection. */
    cleanupESPSecureMgrCerts( &networkContext );
    ( void ) xTlsDisconnect( &networkContext );

    return returnStatus;
}
