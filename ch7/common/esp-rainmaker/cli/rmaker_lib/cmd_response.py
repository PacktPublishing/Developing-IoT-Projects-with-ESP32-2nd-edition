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
import requests
import socket
import urllib.parse

try:
    from rmaker_lib.exceptions import InvalidClassInput, HttpErrorResponse, NetworkError, SSLError, RequestTimeoutError, InvalidJSONError
    from requests.exceptions import Timeout, HTTPError, RequestException
    from rmaker_lib.logger import log
    from rmaker_lib import serverconfig, configmanager
    from rmaker_cmd.node import _check_user_input, _set_node_ids_list
except ImportError as err:
    print("Failed to import ESP Rainmaker library. " + str(err))
    raise err


class CommandResponseRequest:
    """
    CommandResponseRequest class used to instantiate instances of command response requests.
    """

    def __init__(self, session, request_id, node_id, start_id, num_records, nodes, cmd, data, timeout):
        log.info("Initialising command response request")
        self.__request_id = request_id
        self.__node_id = node_id
        self.__start_id = start_id
        self.__num_records = num_records
        self.__nodes = nodes
        self.__cmd = cmd
        self.__data = data
        self.__timeout = timeout
        try:
            self.request_header = {'content-type': 'application/json',
                                   'Authorization': session.id_token}
        except AttributeError:
            raise InvalidClassInput(session, 'Invalid Session Input.\
                                              Expected: type <session object>.\
                                              Received: ')

    def get_cmd_requests(self):
        """
        Call the GET command response request API
        
        :raises HttpErrorResponse: Raised when the HTTP request fails
        :raises SSLError: Raised when invalid SSL certificate is passed
        :raises NetworkError: Raised when internet connection is not available
        :raises RequestTimeoutError: Raised when HTTP Request times out
        :raises Exception: A generic error occurred

        :return: API response
        :rtype: dict
        """
        socket.setdefaulttimeout(25)
        log.info(
            "Getting command response requests for request id : " + self.__request_id)
        path = 'user/nodes/cmd'

        query_parameters = 'request_id=' + self.__request_id
        if self.__node_id is not None:
            query_parameters += '&node_id=' + self.__node_id
        if self.__start_id is not None:
            query_parameters += '&start_id=' + \
                urllib.parse.quote_plus(self.__start_id)
        if self.__num_records is not None:
            query_parameters += '&num_records=' + str(self.__num_records)

        url = serverconfig.HOST + path + '?' + query_parameters
        try:
            log.debug("Get command response request URL : " + url)
            response = requests.get(url=url,
                                    headers=self.request_header,
                                    verify=configmanager.CERT_FILE)
            log.debug("Get command response request response : " + response.text)
            response.raise_for_status()

        except HTTPError as http_err:
            log.debug(http_err)
            raise HttpErrorResponse(response.json())
        except requests.exceptions.SSLError:
            raise SSLError
        except requests.exceptions.ConnectionError:
            raise NetworkError
        except Timeout as time_err:
            log.debug(time_err)
            raise RequestTimeoutError
        except Exception:
            raise Exception(response.text)
        log.info("Fetched command response request successfully.")
        return response.json()

    def create_cmd_request(self):
        """
        Call the POST command response request API

        :raises NetworkError: Invalid JSON received.
        :raises HttpErrorResponse: Raised when the HTTP request fails
        :raises SSLError: Raised when invalid SSL certificate is passed
        :raises NetworkError: Raised when internet connection is not available
        :raises RequestTimeoutError: Raised when HTTP Request times out
        :raises RequestException: There was an ambiguous exception that occurred while handling your request
        :raises Exception: A generic error occurred

        :return: API response
        :rtype: dict
        """
        socket.setdefaulttimeout(25)
        path = 'user/nodes/cmd'

        nodes_without_spaces = self.__nodes.strip()
        # Check user input format
        _ = _check_user_input(nodes_without_spaces)
        # Create list from node ids string
        node_list = _set_node_ids_list(nodes_without_spaces)

        if self.__data is not None:
            # Trimming white spaces except the ones between two strings
            data = re.sub(r"(?<![a-z]|[A-Z])\s(?![a-z]|[A-Z])|\
                (?<=[a-z]|[A-Z])\s(?![a-z]|[A-Z])|\
                    (?<![a-z]|[A-Z])\s(?=[a-z]|[A-Z])", "", self.__data)
            try:
                log.debug('JSON data : ' + data)
                data = json.loads(data)
            except Exception:
                raise InvalidJSONError

        request_payload = {
            'node_ids': node_list,
            'cmd': self.__cmd,
            'data': data
        }

        if self.__timeout is not None:
            request_payload['timeout'] = self.__timeout

        request_url = serverconfig.HOST + path
        try:
            log.debug("Create command response request URL : " +
                      str(request_url)
                      )
            response = requests.post(url=request_url,
                                     data=json.dumps(request_payload),
                                     headers=self.request_header,
                                     verify=configmanager.CERT_FILE,
                                     timeout=(60.0, 60.0))
            log.debug("Create command response request Response : " +
                      str(response.text))
            response.raise_for_status()

        except requests.exceptions.HTTPError as http_err:
            log.debug(http_err)
            raise HttpErrorResponse(response.json())
        except requests.exceptions.SSLError as ssl_err:
            log.debug(ssl_err)
            raise SSLError
        except (ConnectionError, socket.timeout) as conn_err:
            log.debug(conn_err)
            raise NetworkError
        except Timeout as time_err:
            log.debug(time_err)
            raise RequestTimeoutError
        except RequestException as create_cmds_req_err:
            log.debug(create_cmds_req_err)
            raise RequestException
        except Exception as create_cmds_err:
            log.debug(create_cmds_err)
            raise create_cmds_err

        return response.json()
