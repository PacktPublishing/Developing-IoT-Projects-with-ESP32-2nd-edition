/*
 * coreMQTT Agent v1.2.0
 * Copyright (C) 2021 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * @file core_mqtt_agent_config_defaults.h
 * @brief This represents the default values for the configuration macros
 * for the MQTT-Agent library.
 *
 * @note This file SHOULD NOT be modified. If custom values are needed for
 * any configuration macro, a core_mqtt_agent_config.h file should be provided to
 * the MQTT-Agent library to override the default values defined in this file.
 * To use the custom config file, the MQTT_AGENT_DO_NOT_USE_CUSTOM_CONFIG
 * preprocessor macro SHOULD NOT be set.
 */

#ifndef CORE_MQTT_AGENT_CONFIG_DEFAULTS_H_
#define CORE_MQTT_AGENT_CONFIG_DEFAULTS_H_

/* *INDENT-OFF* */
#ifdef __cplusplus
    extern "C" {
#endif
/* *INDENT-ON* */

/* MQTT_AGENT_DO_NOT_USE_CUSTOM_CONFIG allows building the MQTT library
 * without a custom config. If a custom config is provided, the
 * MQTT_AGENT_DO_NOT_USE_CUSTOM_CONFIG macro should be defined. */
#ifndef MQTT_AGENT_DO_NOT_USE_CUSTOM_CONFIG
    /* Include custom config file before other headers. */
    #include "core_mqtt_agent_config.h"
#endif

/* The macro definition for MQTT_AGENT_DO_NOT_USE_CUSTOM_CONFIG is for Doxygen
 * documentation only. */

/**
 * @brief Define this macro to build the MQTT library without the custom config
 * file core_mqtt_agent_config.h.
 *
 * Without the custom config, the MQTT library builds with
 * default values of config macros defined in core_mqtt_agent_config_defaults.h file.
 *
 * If a custom config is provided, then MQTT_AGENT_DO_NOT_USE_CUSTOM_CONFIG should
 * be defined.
 */
#ifdef DOXYGEN
    #define MQTT_AGENT_DO_NOT_USE_CUSTOM_CONFIG
#endif

/**
 * @brief The maximum number of pending acknowledgments to track for a single
 * connection.
 *
 * @note The MQTT agent tracks MQTT commands (such as PUBLISH and SUBSCRIBE) th
 * at are still waiting to be acknowledged.  MQTT_AGENT_MAX_OUTSTANDING_ACKS set
 * the maximum number of acknowledgments that can be outstanding at any one time.
 * The higher this number is the greater the agent's RAM consumption will be.
 *
 * <b>Possible values:</b> Any positive integer up to SIZE_MAX. <br>
 * <b>Default value:</b> `20`
 */
#ifndef MQTT_AGENT_MAX_OUTSTANDING_ACKS
    #define MQTT_AGENT_MAX_OUTSTANDING_ACKS    ( 20U )
#endif

/**
 * @brief Time in milliseconds that the MQTT agent task will wait in the Blocked state (so
 * not using any CPU time) for a command to arrive in its command queue before
 * exiting the blocked state so it can call MQTT_ProcessLoop().
 *
 * @note It is important MQTT_ProcessLoop() is called often if there is known
 * MQTT traffic, but calling it too often can take processing time away from
 * lower priority tasks and waste CPU time and power.
 *
 * <b>Possible values:</b> Any positive 32 bit integer. <br>
 * <b>Default value:</b> `1000`
 */
#ifndef MQTT_AGENT_MAX_EVENT_QUEUE_WAIT_TIME
    #define MQTT_AGENT_MAX_EVENT_QUEUE_WAIT_TIME    ( 1000U )
#endif

/**
 * @brief Whether the agent should configure the coreMQTT library to be used with publishes
 * greater than QoS0. Setting this to 0 will disallow the coreMQTT library to send publishes
 * with QoS > 0.
 *
 * <b>Possible values:</b> 0 or 1 <br>
 * <b>Default value:</b> `1`
 */
#ifndef MQTT_AGENT_USE_QOS_1_2_PUBLISH
    #define MQTT_AGENT_USE_QOS_1_2_PUBLISH    ( 1 )
#endif

/* *INDENT-OFF* */
#ifdef __cplusplus
    }
#endif
/* *INDENT-ON* */

#endif /* ifndef CORE_MQTT_AGENT_CONFIG_DEFAULTS_H_ */
