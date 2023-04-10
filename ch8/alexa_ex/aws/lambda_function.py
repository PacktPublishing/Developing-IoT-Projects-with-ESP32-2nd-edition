
import logging
import time
import json
import uuid
import boto3

endpoint_id = "home_temp_sensor"
logger = logging.getLogger()
logger.setLevel(logging.INFO)
client = boto3.client('iot-data')

discovery_response = {
    "event": {
        "header": {
            "namespace": "Alexa.Discovery",
            "name": "Discover.Response",
            "payloadVersion": "3",
            "messageId": "<message id>"
        },
        "payload": {
            "endpoints": [
                {
                    "endpointId": endpoint_id,
                    "manufacturerName": "iot-with-esp32",
                    "description": "Smart temperature sensor",
                    "friendlyName": "Temperature sensor",
                    "displayCategories": ["TEMPERATURE_SENSOR"],
                    "cookie": {},
                    "capabilities": [
                        {
                            "type": "AlexaInterface",
                            "interface": "Alexa.TemperatureSensor",
                            "version": "3",
                            "properties": {
                                "supported": [
                                    {
                                        "name": "temperature"
                                    }
                                ],
                                "proactivelyReported": True,
                                "retrievable": True
                            }
                        },
                        {
                            "type": "AlexaInterface",
                            "interface": "Alexa.EndpointHealth",
                            "version": "3",
                            "properties": {
                                "supported": [
                                    {
                                        "name": "connectivity"
                                    }
                                ],
                                "proactivelyReported": True,
                                "retrievable": True
                            }
                        },
                        {
                            "type": "AlexaInterface",
                            "interface": "Alexa",
                            "version": "3"
                        }
                    ]
                }
            ]
        }
    }
}

state_report = {
    "event": {
        "header": {
            "namespace": "Alexa",
            "name": "StateReport",
            "messageId": "<message id>",
            "correlationToken": "<an opaque correlation token>",
            "payloadVersion": "3"
        },
        "endpoint": {
            "endpointId": endpoint_id
        },
        "payload": {}
    },
    "context": {
        "properties": [{
            "namespace": "Alexa.TemperatureSensor",
            "name": "temperature",
            "value": {
                    "value": 19.9,
                    "scale": "CELSIUS"
            },
            "timeOfSample": "2017-02-03T16:20:50.52Z",
            "uncertaintyInMilliseconds": 1000
        },
            {
                "namespace": "Alexa.EndpointHealth",
                "name": "connectivity",
                "value": {
                    "value": "OK"
                },
                "timeOfSample": "2017-02-03T16:20:50.52Z",
                "uncertaintyInMilliseconds": 0
        }
        ]
    }
}

accept_grant_response = {
    "event": {
        "header": {
            "namespace": "Alexa.Authorization",
            "name": "AcceptGrant.Response",
            "payloadVersion": "3",
            "messageId": "5f8a426e-01e4-4cc9-8b79-65f8bd0fd8a4"
        },
        "payload": {}
    }
}


def lambda_handler(request, context):
    """Lambda handler for the smart home skill
    """

    try:
        request_namespace = request["directive"]["header"]["namespace"]
        request_name = request["directive"]["header"]["name"]

        if request_namespace == "Alexa.Discovery" and request_name == "Discover":
            response = gen_response(repsonse_blueprint=discovery_response)
        elif request_namespace == "Alexa" and request_name == "ReportState":
            response = gen_report_state(request["directive"]["header"]["correlationToken"])
        elif request_namespace == "Alexa.Authorization" and request_name == "AcceptGrant":
            response = gen_response(repsonse_blueprint=accept_grant_response)
        else:
            logger.error("unexpected request")
            return response

        return response

    except ValueError as error:
        logger.error(error)
        raise


def get_uuid():
    return str(uuid.uuid4())

def get_utc_timestamp(seconds=None):
    return time.strftime("%Y-%m-%dT%H:%M:%S.00Z", time.gmtime(seconds))

def read_temp_thing():
    response = client.get_thing_shadow(thingName=endpoint_id)
    streamingBody = response["payload"].read().decode('utf-8')
    jsonState = json.loads(streamingBody)
    return jsonState["state"]["reported"]["temperature"]

def gen_report_state(tkn):
    response = state_report
    response["event"]["header"]["messageId"] = get_uuid()
    response["event"]["header"]["correlationToken"] = tkn
    ts_str = get_utc_timestamp()
    response["context"]["properties"][0]["timeOfSample"] = ts_str
    response["context"]["properties"][1]["timeOfSample"] = ts_str
    response["context"]["properties"][0]["value"]["value"] = read_temp_thing()
    return response

def gen_response(repsonse_blueprint):
    response = repsonse_blueprint
    response["event"]["header"]["messageId"] = get_uuid()
    return response

