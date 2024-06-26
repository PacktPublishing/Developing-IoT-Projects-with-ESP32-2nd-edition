MQTTAgent_CommandLoop proof
==============

This directory contains a memory safety proof for MQTTAgent_CommandLoop.

The proof runs within 3 minutes on a t2.2xlarge. It provides complete coverage of:
 * MQTTAgent_CommandLoop()
 * MQTTAgent_Init()
 * addAwaitingOperation()
 * getAgentFromMQTTContext()
 * getAwaitingOperation()
 * handleAcks()
 * mqttEventCallback()

For this proof, stubs are used for the implementation of functions in the following interfaces and
function types. Since the implementation for these functions will be provided by the applications,
the proof only will require stubs.
 * MQTTAgentMessageInterface_t
 * TransportInterface_t
 * MQTTGetCurrentTimeFunc_t
 * MQTTAgentIncomingPublishCallback_t
 * MQTTAgentCommandCallback_t

 In addition to the interfaces and the function types, stubs are used for the below listed functions.
 CBMC proofs are written for these functions separately.
 * MQTTAgentCommand_ProcessLoop()
 * MQTTAgentCommand_Publish()
 * MQTTAgentCommand_Subscribe()
 * MQTTAgentCommand_Unsubscribe()
 * MQTTAgentCommand_Connect()
 * MQTTAgentCommand_Disconnect()
 * MQTTAgentCommand_Ping()
 * MQTTAgentCommand_Terminate()
 * MQTT_ProcessLoop()
 * MQTT_Init()

To run the proof.
-------------

* Add `cbmc`, `goto-cc`, `goto-instrument`, `goto-analyzer`, and `cbmc-viewer`
  to your path.
* Run `make`.
* Open html/index.html in a web browser.

To use [`arpa`](https://github.com/awslabs/aws-proof-build-assistant) to simplify writing Makefiles.
-------------

* Run `make arpa` to generate a Makefile.arpa that contains relevant build information for the proof.
* Use Makefile.arpa as the starting point for your proof Makefile by:
  1. Modifying Makefile.arpa (if required).
  2. Including Makefile.arpa into the existing proof Makefile (add `sinclude Makefile.arpa` at the bottom of the Makefile, right before `include ../Makefile.common`).
