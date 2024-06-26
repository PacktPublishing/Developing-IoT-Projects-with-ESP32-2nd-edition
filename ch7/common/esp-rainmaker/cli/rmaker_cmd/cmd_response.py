# Copyright 2020 Espressif Systems (Shanghai) PTE LTD
#
# Licensed under the Apache License, Version 2.0 (the "License');
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

try:
    from rmaker_lib import session
    from rmaker_lib.logger import log
    from rmaker_lib import cmd_response
except ImportError as err:
    print("Failed to import ESP Rainmaker library. " + str(err))
    raise err


def get_cmd_requests(vars=None):
    """
    Get command response requests and print the response

    :param vars: A dictionary of all parameters that the user has specified, defaults to None
    :type vars: dict, optional
    """    
    try:
        cmd = cmd_response.CommandResponseRequest(session.Session(
        ), vars["request_id"], vars["node_id"], vars["start_id"], vars["num_records"], None, None, None, None)
        cmd_resp = cmd.get_cmd_requests()
    except Exception as get_cmd_err:
        log.error(get_cmd_err)
    else:
        for key, val in cmd_resp.items():
            title = key.replace("_", " ").title()
            print("{}: {}".format(title, val))
        print("(This is in Beta)")


def create_cmd_request(vars=None):
    """
    Create a command response request and print the response

    :param vars: A dictionary of all parameters that the user has specified, defaults to None
    :type vars: dict, optional
    """    
    try:
        cmd = cmd_response.CommandResponseRequest(session.Session(
        ), None, None, None, None, vars["nodes"], vars["cmd"], vars["data"], vars["timeout"])
        cmd_resp = cmd.create_cmd_request()
    except Exception as create_cmd_err:
        log.error(create_cmd_err)
    else:
        for key, val in cmd_resp.items():
            title = key.replace("_", " ").title()
            print("{}: {}".format(title, val))
        print("(This is in Beta)")
