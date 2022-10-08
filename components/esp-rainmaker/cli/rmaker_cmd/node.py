# Copyright 2020 Espressif Systems (Shanghai) PTE LTD
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

import json
import re
import os
import sys
import time
import datetime
import requests
import base64
import re
from pathlib import Path

try:
    from rmaker_lib import session, node, device, service,\
        serverconfig, configmanager
    from rmaker_lib.exceptions import HttpErrorResponse, NetworkError, InvalidJSONError, SSLError,\
        RequestTimeoutError
    from rmaker_lib.logger import log
    from rmaker_tools.rmaker_claim.claim import claim
except ImportError as err:
    print("Failed to import ESP Rainmaker library. " + str(err))
    raise err

MAX_HTTP_CONNECTION_RETRIES = 5

def get_nodes(vars=None):
    """
    List all nodes associated with the user.

    :param vars: No Parameters passed, defaults to `None`
    :type vars: dict | None

    :raises Exception: If there is an HTTP issue while getting nodes

    :return: None on Success
    :rtype: None
    """
    try:
        s = session.Session()
        nodes = s.get_nodes()
    except Exception as get_nodes_err:
        log.error(get_nodes_err)
    else:
        if len(nodes.keys()) == 0:
            print('User is not associated with any nodes.')
            return
        for key in nodes.keys():
            print(nodes[key].get_nodeid())
    return

def _check_user_input(node_ids_str):
    log.debug("Check user input....")
    # Check user input format
    input_pattern = re.compile("^[0-9A-Za-z]+(,[0-9A-Za-z]+)*$")
    result = input_pattern.match(node_ids_str)
    log.debug("User input result: {}".format(result))
    if result is None:
        sys.exit("Invalid format. Expected: <nodeid>,<nodeid>,... (no spaces)")
    return True         

def _print_api_error(node_json_resp):
    print("{:<7} ({}):  {}".format(
        node_json_resp['status'].capitalize(),
        node_json_resp['error_code'],
        node_json_resp['description'])
        )

def _set_node_ids_list(node_ids):
    # Create list from node ids string
    node_id_list = node_ids.split(',')
    node_id_list = [ item.strip() for item in node_id_list ]
    log.debug("Node ids list: {}".format(node_id_list))
    return node_id_list

def sharing_request_op(accept_request=False, request_id=None):
    """
    Accept or decline sharing request
    
    :param vars: `accept_request` as key
                  If true, accept sharing request
                  If false, decline sharing request
    :type vars: bool

    :param vars: `request_id` as key - Id of sharing request
    :type vars: str

    :raises Exception: If there is an issue
                       accepting or declining request

    :return: API response
    :rtype: dict
    """
    log.debug("Accept sharing request")

    print('\nPlease make sure current (logged-in) user is Secondary user\n')

    if accept_request:
        print("Accepting request")
    else:
        print("Declining request")

    # Create API data dictionary
    api_data = {}
    api_data['accept'] = accept_request
    api_data['request_id'] = request_id

    node_obj = node.Node(None, session.Session())
    log.debug("API data set: {}".format(api_data))
    
    # API to accept or decline node sharing request
    node_json_resp = node_obj.request_op(api_data)
    log.debug("Sharing request API response: {}".format(node_json_resp))

    return node_json_resp

def list_sharing_details(node_id=None, primary_user=False, request_id=None, list_requests=False):
    """
    List sharing details of all nodes associated with user
    or List pending requests
    
    :param vars: `node_id` as key - Node Id of the node(s)
                 (if not provided, is set to all nodes associated with user)
    :type vars: str

    :param vars: `primary_user` as key - User is primary or secondary
                 (if provided, user is primary user)
    :type vars: bool

    :param vars: `request_id` as key - Id of sharing request
    :type vars: str

    :param vars: `list_requests` as key -
                 If True, list pending requests
                 If False, list sharing details of nodes
    :type vars: bool

    :raises Exception: If there is an issue
                       while listing details

    :return: API response
    :rtype: dict
    """
    node_obj = node.Node(node_id, session.Session())
    log.debug("Node id received from user: {}".format(node_id))

    # Set data for listing pending requests
    if list_requests:
        # Create API query params
        api_params = {}
        if request_id:
            api_params['id'] = request_id
        api_params['primary_user'] = "{}".format(primary_user)

        node_json_resp = node_obj.get_shared_nodes_request(api_params)
        log.debug("List sharing request response: {}".format(node_json_resp))
    else:
        # Get sharing details of all nodes associated with user
        # API
        node_json_resp = node_obj.get_sharing_details_of_nodes()
        log.debug("Get shared nodes response: {}".format(node_json_resp))

    return node_json_resp

def add_user_to_share_nodes(nodes=None, user=None):
    """
    Add user to share nodes
    
    :param vars: `nodes` as key - Node Id of the node(s)
    :type vars: str

    :param vars: `user` as key - User name
    :type vars: str

    :raises Exception: If there is an issue
                       while adding user to share nodes

    :return: API response
    :rtype: dict
    """
    log.debug("Adding user to share nodes")

    # Remove any spaces if exist
    nodes = nodes.strip()
    # Check user input format
    ret_status = _check_user_input(nodes)
    # Create list from node ids string
    node_id_list = _set_node_ids_list(nodes)
    log.debug("Node ids list: {}".format(node_id_list))

    log.debug("User name is set: {}".format(user))
    
    # Create API input info
    api_input = {}
    api_input['nodes'] = node_id_list
    api_input['user_name'] = user
    log.debug("API data set: {}".format(api_input))

    # API
    node_obj = node.Node(None, session.Session())
    node_json_resp = node_obj.add_user_for_sharing(api_input)
    log.debug("Set shared nodes response: {}".format(node_json_resp))

    return node_json_resp

def remove_sharing(nodes=None, user=None, request_id=None):
    """
    Remove user from shared nodes or
    Remove sharing request

    :param vars: `nodes` as key - Node Id for the node
    :type vars: str

    :param vars: `user` as key - User name
    :type vars: str

    :param vars: `request_id` as key - Id of sharing request
    :type vars: str

    :raises Exception: If there is an issue
                       while remove operation

    :return: API response
    :rtype: dict
    """
    print('\nPlease make sure current (logged-in) user is Primary user\n')

    node_json_resp = None
    node_obj = node.Node(None, session.Session())
    if request_id:
        # API call to remove the shared nodes request
        node_json_resp = node_obj.remove_shared_nodes_request(request_id)
        log.debug("Remove sharing request response: {}".format(node_json_resp))
    else:
        # Remove any spaces if exist
        node_ids = nodes.strip()

        # Check user input format
        ret_status = _check_user_input(node_ids)
        
        # Create API query params dictionary
        api_params = {}
        api_params['nodes'] = node_ids
        api_params['user_name'] = user
        log.debug("API data set to: {}".format(api_params))
        
        # API call to remove the shared nodes
        node_json_resp = node_obj.remove_user_from_shared_nodes(api_params)
        log.debug("Remove user from shared nodes response: {}".format(node_json_resp))
    
    return node_json_resp

def _get_status(resp):
    return(resp['status'].capitalize())

def _get_description(resp):
    return(resp['description'])

def _get_request_id(resp):
    return(resp['request_id'])

def _get_request_expiration(request):
    total_expiry_days = 7
    expiration_str = ""

    curr_time = datetime.datetime.now()
    log.debug("Current time is set to: {}".format(curr_time))

    creation_time = datetime.datetime.fromtimestamp(request['request_timestamp'])
    log.debug("Creation timestamp received : {}".format(creation_time))

    timedelta = curr_time - creation_time
    log.debug("Timedelta is : {}".format(timedelta))
    days_left = total_expiry_days - timedelta.days
    log.debug("Days left for request to expire: {}".format(days_left))
    if days_left <= 0:
        expiration_str = "** Request expired **"
    elif days_left == 1:
        expiration_str = "** Request will expire today **"
    else:
        expiration_str = "** Request will expire in {} day(s) **".format(days_left)
    log.debug("Expiration is: {}".format(expiration_str))
    return expiration_str

def _print_request_details(resp, is_primary_user=False):
    try:
        log.debug("Printing request details")
        requests_in_resp = resp['sharing_requests']
        request_exists = False
        if not requests_in_resp:
            print("No pending requests")
            return
        for request in requests_in_resp:
            nodes_str = ""
            if request['request_status'].lower() == 'declined':
                continue
            request_exists = True
            print("\n{:<12}: {}".format('Request Id',request['request_id']))
            for n_id in request['node_ids']:
                nodes_str += "{},".format(n_id)
            nodes_str = nodes_str.rstrip(',')
            print("{:<12}: {}".format('Node Id(s)', nodes_str))
            if is_primary_user:
                print("{:<12}: {}".format('Shared with', request['user_name']))
            else:
                print("{:<12}: {}".format('Shared by', request['primary_user_name']))
            expiration_msg = _get_request_expiration(request)
            print(expiration_msg)

        if not request_exists:
            print("No pending requests")

    except KeyError as err:
        print(err)
        log.debug("Key Error while printing request details: {}".format(err))
        print("Error in displaying details...Please check API Json...Exiting...")
        sys.exit(0)
    log.debug("Done printing request details")

def _print_sharing_details(resp):
    try:
        log.debug("Printing sharing details of nodes")
        nodes_in_resp = resp['node_sharing']
        for nodes in nodes_in_resp:
            primary_users = ""
            secondary_users = ""
            print("\nNode Id: {}".format(nodes['node_id']))

            for user in nodes['users']['primary']:
                primary_users += "{},".format(user)
            primary_users = primary_users.rstrip(',')
            print("{:<7}: {:<9}: {}".format('Users', 'Primary', primary_users), end='')

            if 'secondary' in nodes['users'].keys():
                for user in nodes['users']['secondary']:
                    secondary_users += "{},".format(user)
                secondary_users = secondary_users.rstrip(',')
                print("\n{:>18}: {}".format('Secondary', secondary_users), end='')
            print()

    except KeyError as err:
        log.debug("Key Error while printing sharing details of nodes: {}".format(err))
        print("Error in displaying details...Please check API Json...Exiting...")
        sys.exit(0)
    log.debug("Done printing sharing details of nodes")

'''
Node Sharing operations based on user input
'''
def node_sharing_ops(vars=None):
    try:
        op = ""

        log.debug("Performing Node Sharing operations")

        # Set action if given
        try:
            action = vars['sharing_ops'].lower()
        except AttributeError:
            print(vars['parser'].format_help())
            sys.exit(0)
        
        # Set operation to base action
        op = action

        if action == 'add_user':
            # Share nodes with user
            print("Adding user to share node(s)")
            node_json_resp = add_user_to_share_nodes(nodes=vars['nodes'], user=vars['user'])
            
            # Print success response
            if 'status' in node_json_resp and node_json_resp['status'].lower() == 'success':
                print("{:<11}: {}\n{:<11}: {}".format(
                    _get_status(node_json_resp),
                    _get_description(node_json_resp),
                    'Request Id',
                    _get_request_id(node_json_resp))
                    )
        elif action == "accept":
            # Accept sharing request
            node_json_resp = sharing_request_op(accept_request=True, request_id=vars['id'])

            # Print success response
            if 'status' in node_json_resp and node_json_resp['status'].lower() == 'success':
                print("{:<11}: {}".format(
                    _get_status(node_json_resp),
                    _get_description(node_json_resp))
                    )
        elif action == "decline":
            # Decline sharing request
            node_json_resp = sharing_request_op(accept_request=False, request_id=vars['id'])

            # Print success response
            if 'status' in node_json_resp and node_json_resp['status'].lower() == 'success':
                print("{:<11}: {}".format(
                    _get_status(node_json_resp),
                    _get_description(node_json_resp))
                    )
        elif action == "cancel":
            log.debug("Performing action: {}".format(action))
            # Cancel sharing request
            print("Cancelling request")
            node_json_resp = remove_sharing(request_id=vars['id'])

            # Print success response
            if 'status' in node_json_resp and node_json_resp['status'].lower() == 'success':
                print("{}: {}".format(
                    _get_status(node_json_resp),
                    _get_description(node_json_resp))
                    )
        elif action == "remove_user":
            log.debug("Performing action: {}".format(action))
            # Remove nodes shared with user
            print("Removing user from shared nodes")
            node_json_resp = remove_sharing(nodes=vars['nodes'], user=vars['user'])
            
            # Print success response
            if 'status' in node_json_resp and node_json_resp['status'].lower() == 'success':
                print("{}: {}".format(
                    _get_status(node_json_resp),
                    _get_description(node_json_resp))
                    )
        elif action == "list_nodes":
            log.debug("Performing action: {}".format(action))

            log.debug("List sharing details of nodes associated with user")
            print("Displaying sharing details")
            # List sharing details of all nodes associated with user
            node_json_resp = list_sharing_details(node_id=vars['node'])

            # Print success response
            if 'node_sharing' in node_json_resp:
                _print_sharing_details(node_json_resp)
        elif action == "list_requests":
            log.debug("Performing action: {}".format(action))

            log.debug("List pending requests")
            print("Displaying pending requests")
            if vars['primary_user']:
                print("Current (logged-in) user is set as Primary user")
            else:
                print("Current (logged-in) user is set as Secondary user")
            # List pending sharing requests
            node_json_resp = list_sharing_details(primary_user=vars['primary_user'],
                                                    request_id=vars['id'],
                                                    list_requests=True
                                                    )
            # Print success response
            if 'sharing_requests' in node_json_resp:
                _print_request_details(node_json_resp, is_primary_user=vars['primary_user'])

    except Exception as get_node_status_err:
        log.error(get_node_status_err)
        return
    else:
        if 'status' in node_json_resp and node_json_resp['status'].lower() != 'success':
            log.debug("Operation {} failed\nresp: {}".format(op, node_json_resp))
            _print_api_error(node_json_resp)
            return
    log.debug("Operation `{}` was successful".format(op))

def get_node_config(vars=None):
    """
    Shows the configuration of the node.

    :param vars: `nodeid` as key - Node ID for the node, defaults to `None`
    :type vars: dict | None

    :raises Exception: If there is an HTTP issue while getting node config

    :return: None on Success
    :rtype: None
    """
    try:
        node_config = None
        n = node.Node(vars['nodeid'], session.Session())
        node_config = n.get_node_config()
    except Exception as get_nodes_err:
        log.error(get_nodes_err)
    else:
        print(json.dumps(node_config, indent=4))
    return node_config


def get_node_status(vars=None):
    """
    Shows the online/offline status of the node.

    :param vars: `nodeid` as key - Node ID for the node, defaults to `None`
    :type vars: dict | None

    :raises Exception: If there is an HTTP issue while getting node status

    :return: None on Success
    :rtype: None
    """
    try:
        n = node.Node(vars['nodeid'], session.Session())
        node_status = n.get_node_status()
    except Exception as get_node_status_err:
        log.error(get_node_status_err)
    else:
        print(json.dumps(node_status, indent=4))
    return


def set_params(vars=None):
    """
    Set parameters of the node.

    :param vars:
        `nodeid` as key - Node ID for the node,\n
        `data` as key - JSON data containing parameters to be set `or`\n
        `filepath` as key - Path of the JSON file containing parameters
                            to be set,\n
        defaults to `None`
    :type vars: dict | None

    :raises Exception: If there is an HTTP issue while setting params or
                       JSON format issue in HTTP response

    :return: None on Success
    :rtype: None
    """
    log.info('Setting params of the node with nodeid : ' + vars['nodeid'])
    if 'data' in vars:
        data = vars['data']
    if 'filepath' in vars:
        filepath = vars['filepath']

    if data is not None:
        log.debug('Setting node parameters using JSON data.')
        # Trimming white spaces except the ones between two strings
        data = re.sub(r"(?<![a-z]|[A-Z])\s(?![a-z]|[A-Z])|\
            (?<=[a-z]|[A-Z])\s(?![a-z]|[A-Z])|\
                (?<![a-z]|[A-Z])\s(?=[a-z]|[A-Z])", "", data)
        try:
            log.debug('JSON data : ' + data)
            data = json.loads(data)
        except Exception:
            raise InvalidJSONError
            return

    elif filepath is not None:
        log.debug('Setting node parameters using JSON file.')
        file = Path(filepath)
        if not file.exists():
            log.error('File %s does not exist!' % file.name)
            return
        with open(file) as fh:
            try:
                data = json.load(fh)
                log.debug('JSON filename :' + file.name)
            except Exception:
                raise InvalidJSONError
                return

    try:
        n = node.Node(vars['nodeid'], session.Session())
        status = n.set_node_params(data)
    except SSLError:
        log.error(SSLError())
    except NetworkError as conn_err:
        print(conn_err)
        log.warn(conn_err)
    except Exception as set_params_err:
        log.error(set_params_err)
    else:
        print('Node state updated successfully.')
    return


def get_params(vars=None):
    """
    Get parameters of the node.

    :param vars: `nodeid` as key - Node ID for the node, defaults to `None`
    :type vars: dict | None

    :raises Exception: If there is an HTTP issue while getting params or
                       JSON format issue in HTTP response

    :return: None on Success
    :rtype: None
    """
    try:
        params = None
        n = node.Node(vars['nodeid'], session.Session())
        params = n.get_node_params()
    except SSLError:
        log.error(SSLError())
    except NetworkError as conn_err:
        print(conn_err)
        log.warn(conn_err)
    except Exception as get_params_err:
        log.error(get_params_err)
    else:
        if params is None:
            log.error('Node status not updated.')
            return
        else:
            print(json.dumps(params, indent=4))
    return params


def remove_node(vars=None):
    """
    Removes the user node mapping.

    :param vars: `nodeid` as key - Node ID for the node, defaults to `None`
    :type vars: dict | None

    :raises NetworkError: If there is a network connection issue during
                          HTTP request for removing node
    :raises Exception: If there is an HTTP issue while removing node or
                       JSON format issue in HTTP response

    :return: None on Success
    :rtype: None
    """
    log.info('Removing user node mapping for node ' + vars['nodeid'])
    try:
        n = node.Node(vars['nodeid'], session.Session())
        params = n.remove_user_node_mapping()
    except Exception as remove_node_err:
        log.error(remove_node_err)
    else:
        log.debug('Removed the user node mapping successfully.')
        print('Removed node ' + vars['nodeid'] + ' successfully.')
    return


def get_mqtt_host(vars=None):
    """
    Returns MQTT Host endpoint

    :param vars: No Parameters passed, defaults to `None`
    :type vars: dict | None

    :raises NetworkError: If there is a network connection issue while
                          getting MQTT Host endpoint
    :raises Exception: If there is an HTTP issue while getting
                       MQTT Host endpoint or JSON format issue in HTTP response

    :return: MQTT Host endpoint
    :rtype: str
    """
    log.info("Getting MQTT Host endpoint.")
    path = 'mqtt_host'
    request_url = serverconfig.HOST.split(serverconfig.VERSION)[0] + path
    try:
        log.debug("Get MQTT Host request url : " + request_url)
        response = requests.get(url=request_url,
                                verify=configmanager.CERT_FILE)
        log.debug("Get MQTT Host response : " + response.text)
        response.raise_for_status()

    except requests.exceptions.HTTPError as http_err:
        log.debug(http_err)
        raise HttpErrorResponse(response.json())
    except requests.exceptions.SSLError:
        raise SSLError
    except requests.ConnectionError:
        raise NetworkError
        return
    except Exception as mqtt_host_err:
        log.error(mqtt_host_err)
        return
    try:
        response = json.loads(response.text)
    except Exception as json_decode_err:
        log.error(json_decode_err)
    if 'mqtt_host' in response:
        log.info("Received MQTT Host endpoint successfully.")
        print(response['mqtt_host'])
    else:
        log.error("MQTT Host does not exists.")
    return response['mqtt_host']


def claim_node(vars=None):
    """
    Claim the node connected to the given serial port
    (Get cloud credentials)

    :param vars: `port` as key - Serial Port, defaults to `None`
    :type vars: str | None

    :raises Exception: If there is an HTTP issue while claiming

    :return: None on Success
    :rtype: None
    """
    try:
        if not vars['port'] and not vars['mac'] and not vars['addr'] and not vars['platform']:
            sys.exit(vars['parser'].print_help())
        if vars['addr'] and not vars['port'] and not vars['platform']:
            sys.exit('Invalid. <port> or --platform argument is needed.')
        if vars['port']:
            if not vars['mac'] and not vars['platform']:
                claim(port=vars['port'], node_platform=vars['platform'], mac_addr=vars['mac'], flash_address=vars['addr'])
                return
        if (vars['mac'] and not vars['platform']):
            sys.exit("Invalid. --platform argument needed.")
        if (not vars['mac'] and vars['platform']):
            sys.exit("Invalid. --mac argument needed.")
        if vars['mac']:
            if not re.match(r'([0-9A-F]:?){12}', vars['mac']):
                sys.exit('Invalid MAC address.')
        claim(port=vars['port'], node_platform=vars['platform'], mac_addr=vars['mac'], flash_address=vars['addr'])
    except Exception as claim_err:
        log.error(claim_err)
        return

def ota_upgrade(vars=None):
    """
    Upload OTA Firmware Image
    and
    Set image url returned in response as node params
    """
    try:
        node_id = vars['nodeid']
        img_file_path = vars['otaimagepath']
        if os.path.isabs(img_file_path) is False:
            img_file_path = os.path.join(os.getcwd(), img_file_path)
        img_name = img_file_path.split('/')[-1].split('.bin')[0]
        with open(img_file_path, 'rb') as f:
            fw_img_bytes = f.read()
        base64_fw_img = base64.b64encode(fw_img_bytes).decode('ascii')

        retries = MAX_HTTP_CONNECTION_RETRIES
        node_object = None
        status = None
        response = None
        service_name = None
        service_obj = None
        service_config = None
        node_params = None
        param_url_to_set = None
        curr_session = None
        while retries > 0:
            try:
                # If session is expired then to initialise the new session
                # internet connection is required.
                if not curr_session:
                    curr_session = session.Session()
                if not node_object:
                    node_object = node.Node(node_id, curr_session)
                    log.info("Creating service object...")
                if not service_obj:
                    service_obj = service.Service()
                    log.info("Checking service " + service.OTA_SERVICE_TYPE + " in node config...")
                    print("Checking " + service.OTA_SERVICE_TYPE + " in node config...")
                if not service_config and not service_name:
                    service_config, service_name = service_obj.verify_service_exists(node_object, service.OTA_SERVICE_TYPE)
                    if not service_config:
                        log.error(service.OTA_SERVICE_TYPE + " not found.")
                        break
                    log.info("Checking service " + service.OTA_SERVICE_TYPE + " in config...Success")
                    log.debug("Service config received: " + str(service_config) +
                              " Service name received: " + str(service_name))
                    print("Uploading OTA Firmware Image...This may take time...")
                    log.info("Uploading OTA Firmware Image...This may take time...")
                if not status and not response:
                    # Upload OTA Firwmare Image
                    status, response = service_obj.upload_ota_image(node_object, img_name, base64_fw_img)
                    if status:
                        break
            except SSLError:
                log.error(SSLError())
                break
            except (NetworkError, RequestTimeoutError) as conn_err:
                print(conn_err)
                log.warn(conn_err)
            except Exception as node_init_err:
                log.error(node_init_err)
                break
            time.sleep(5)
            retries -= 1
            if retries:
                print("Retries left:", retries)
                log.info("Retries left: " + str(retries))

        if node_object is None:
            log.error('Initialising new session...Failed\n')
            return

        if not status or not 'success' in status:
            print("\n")
            log.error("OTA Upgrade...Failed")
            log.debug('OTA Upgrade...Failed '
                      'status: ' + str(status) + ' response: ' + str(response))
            return

        log.info('Upload OTA Firmware Image Request...Success')
        log.debug("Upload OTA Firmware Image Request - Status: " + json.dumps(status) +
                  " Response: " + json.dumps(response))


        retries = MAX_HTTP_CONNECTION_RETRIES
        ota_start_status = None
        node_params = None
        service_read_params = None
        service_write_params = None
        ota_status = None

        while retries > 0:
            try:
                if 'image_url' in response:
                    param_url_to_set = response["image_url"]

                    if not service_read_params and not service_write_params:
                        log.info("Getting service params from node config")
                        service_read_params, service_write_params = service_obj.get_service_params(service_config)
                        log.debug("Service params received with read properties: " + str(service_read_params) +
                                  " Service params received with write properties: " + str(service_write_params))
                        log.info("Getting node params...")
                    if not node_params:
                        node_params = node_object.get_node_params()
                        log.debug("Node params received: " + json.dumps(node_params))
                        print("Setting the OTA URL parameter...")

                    if not ota_start_status:
                        ota_start_status = service_obj.start_ota(node_object, node_params, service_name,
                                                        service_write_params, param_url_to_set)
                        log.debug("OTA status received: " + str(ota_start_status))
                        if not ota_start_status:
                            log.error("Failed to start OTA service...Exiting...")
                            break
                        print("Getting OTA Status...")
                    if not ota_status:
                        ota_status = service_obj.check_ota_status(node_object, service_name, service_read_params)
                        break
            except SSLError:
                log.error(SSLError())
                break
            except (NetworkError, RequestTimeoutError) as conn_err:
                print(conn_err)
                log.warn(conn_err)
            except Exception as node_init_err:
                log.error(node_init_err)
                break
            time.sleep(5)
            retries -= 1
            if retries:
                print("Retries left:", retries)
                log.info("Retries left: " + str(retries))

        if ota_status in [None, False]:
            log.error("OTA Upgrade...Failed")
            log.debug('OTA Upgrade...Failed '
                      'ota_status: ' + str(ota_status))
    except KeyError as key_err:
        log.error("Key Error: " + str(key_err))
    except Exception as ota_err:
        log.error(ota_err)
    return
