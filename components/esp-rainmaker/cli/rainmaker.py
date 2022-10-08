#!/usr/bin/env python3
#
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

import sys
import argparse
from rmaker_cmd.node import *
from rmaker_cmd.user import signup, login, forgot_password,\
                            get_user_details, logout
from rmaker_cmd.provision import provision
from rmaker_cmd.test import test
from rmaker_lib.logger import log


def main():
    parser = argparse.ArgumentParser(formatter_class=argparse.RawTextHelpFormatter)
    parser.set_defaults(func=None)
    subparsers = parser.add_subparsers(help='Functions')

    signup_parser = subparsers.add_parser("signup",
                                          help="Sign up for ESP Rainmaker")
    signup_parser.add_argument('email',
                               type=str,
                               metavar='<email>',
                               help='Email address of the user')
    signup_parser.set_defaults(func=signup)

    login_parser = subparsers.add_parser("login",
                                         help="Login to ESP Rainmaker")
    login_parser.add_argument('--email',
                              type=str,
                              metavar='<email>',
                              help='Email address of the user')
    login_parser.set_defaults(func=login)

    logout_parser = subparsers.add_parser("logout",
                                         help="Logout current (logged-in) user")
    logout_parser.set_defaults(func=logout)


    forgot_password_parser = subparsers.add_parser("forgotpassword",
                                                   help="Reset the password")
    forgot_password_parser.add_argument('email',
                                        type=str,
                                        metavar='<email>',
                                        help='Email address of the user')
    forgot_password_parser.set_defaults(func=forgot_password)

    getnodes_parser = subparsers.add_parser('getnodes',
                                            help='List all nodes associated'
                                                  ' with the user')
    getnodes_parser.set_defaults(func=get_nodes)

    # Node Config
    getnodeconfig_parser = subparsers.add_parser('getnodeconfig',
                                                 help='Get node configuration')
    getnodeconfig_parser.add_argument('nodeid',
                                      type=str,
                                      metavar='<nodeid>',
                                      help='Node ID for the node')
    getnodeconfig_parser.set_defaults(func=get_node_config)

    getnodestatus_parser = subparsers.add_parser('getnodestatus',
                                                 help='Get online/offline'
                                                       ' status of the node')
    getnodestatus_parser.add_argument('nodeid',
                                      type=str,
                                      metavar='<nodeid>',
                                      help='Node ID for the node')
    getnodestatus_parser.set_defaults(func=get_node_status)

    setparams_parser = subparsers.add_parser('setparams',
                                             help='Set node parameters'
                                                   ' \nNote: Enter JSON data in'
                                                   ' single quotes')
    setparams_parser.add_argument('nodeid',
                                  metavar='<nodeid>',
                                  help='Node ID for the node')
    setparams_parser = setparams_parser.add_mutually_exclusive_group(
        required=True)

    setparams_parser.add_argument('--filepath',
                                  help='Path of the JSON file\
                                        containing parameters to be set')
    setparams_parser.add_argument('--data',
                                  help='JSON data containing parameters\
                                        to be set. Note: Enter JSON data\
                                        in single quotes')
    setparams_parser.set_defaults(func=set_params)

    getparams_parser = subparsers.add_parser('getparams',
                                             help='Get node parameters')
    getparams_parser.add_argument('nodeid',
                                  type=str,
                                  metavar='<nodeid>',
                                  help='Node ID for the node')
    getparams_parser.set_defaults(func=get_params)

    remove_node_parser = subparsers.add_parser('removenode',
                                               help='Remove user node mapping')
    remove_node_parser.add_argument('nodeid',
                                    type=str,
                                    metavar='<nodeid>',
                                    help='Node ID for the node')
    remove_node_parser.set_defaults(func=remove_node)

    provision_parser = subparsers.add_parser('provision',
                                             help='Provision the node'
                                                   ' to join Wi-Fi network')
    provision_parser.add_argument('pop',
                                  type=str,
                                  metavar='<pop>',
                                  help='Proof of possesion for the node')
    provision_parser.set_defaults(func=provision)

    getmqtthost_parser = subparsers.add_parser('getmqtthost',
                                               help='Get the MQTT Host URL'
                                                     ' to be used in the'
                                                     ' firmware')
    getmqtthost_parser.set_defaults(func=get_mqtt_host)

    claim_parser = subparsers.add_parser('claim',
                                         help='Claim the node connected to the given serial port'
                                              ' \n(Get cloud credentials)')

    claim_parser.add_argument("port", metavar='<port>',
                              default=None,
                              help='Serial Port connected to the device.'
                                   '\nUsage: ./rainmaker.py claim <port> [<optional arguments>]',
                              nargs='?')

    claim_parser.add_argument("--platform",
                              choices=['esp32', 'esp32s2', 'esp32s3', 'esp32c3'],
                              type=str,
                              help='Node platform.')

    claim_parser.add_argument("--mac", metavar='<mac>',
                              type=str,
                              help='Node MAC address in the format AABBCC112233.')

    claim_parser.add_argument("--addr", metavar='<flash-address>',
                              help='Address in the flash memory where the claim data will be written.\nDefault: 0x340000')
    claim_parser.set_defaults(func=claim_node, parser=claim_parser)

    test_parser = subparsers.add_parser('test',
                                        help='Test commands to check'
                                              ' user node mapping')
    test_parser.add_argument('--addnode',
                             metavar='<nodeid>',
                             help='Add user node mapping')
    test_parser.set_defaults(func=test)
    
    upload_ota_image_parser = subparsers.add_parser('otaupgrade',
                                                    help='Upload OTA Firmware image and start OTA Upgrade')
    upload_ota_image_parser.add_argument('nodeid',
                                         type=str,
                                         metavar='<nodeid>',
                                         help='Node ID for the node')
    upload_ota_image_parser.add_argument('otaimagepath',
                                        type=str,
                                        metavar='<ota_image_path>',
                                        help='OTA Firmware image path')
    upload_ota_image_parser.set_defaults(func=ota_upgrade)

    user_info_parser = subparsers.add_parser("getuserinfo",
                                         help="Get details of current (logged-in) user")
    user_info_parser.set_defaults(func=get_user_details)

    # Node Sharing
    sharing_parser = subparsers.add_parser('sharing',
                                            help='Node Sharing Operations',
                                            formatter_class=argparse.RawTextHelpFormatter,
                                            epilog="\nUser Login: \n\tCurrent (logged-in) user must be "
                                                 "a primary or secondary user to the node(s)\n\t"
                                                 "while performing the sharing operations")

    sharing_parser.set_defaults(func=node_sharing_ops, parser=sharing_parser)

    sharing_subparser = sharing_parser.add_subparsers(dest="sharing_ops")

    # Share node with user
    add_op_parser = sharing_subparser.add_parser('add_user',
                                                 help='Request to add user for sharing the node(s)',
                                                 formatter_class=argparse.RawTextHelpFormatter,
                                                 description="Send request to add user for the node(s)")

    add_op_parser.add_argument('--user',
                               type=str,
                               metavar='<user_name>',
                               help='User Name (Email) of secondary user',
                               required=True)
    
    add_op_parser.add_argument('--nodes',
                               type=str,
                               metavar='<node_ids>',
                               help="Node Id's of node(s)\n"
                               "format: <nodeid1>,<nodeid2>,...",
                               required=True)
    
    add_op_parser.set_defaults(func=node_sharing_ops, parser=add_op_parser)


    # Remove shared nodes with user
    remove_user_op_parser = sharing_subparser.add_parser('remove_user',
                                                            help='Remove user from shared node(s)',
                                                            formatter_class=argparse.RawTextHelpFormatter,
                                                            description='Remove user from shared node(s)')

    remove_user_op_parser.add_argument('--user',
                                       type=str,
                                       metavar='<user_name>',
                                       help='User Name (Email) of secondary user',
                                       required=True)

    remove_user_op_parser.add_argument('--nodes',
                                       type=str,
                                       metavar='<node_ids>',
                                       help="Node Id's of shared node(s)\n"
                                       "format: <nodeid1>,<nodeid2>,...",
                                       required=True)

    remove_user_op_parser.set_defaults(func=node_sharing_ops, parser=remove_user_op_parser)


    # Accept sharing request
    add_accept_op_parser = sharing_subparser.add_parser('accept',
                                                         help='Accept sharing request(s)',
                                                         formatter_class=argparse.RawTextHelpFormatter,
                                                         description="Accept request for sharing node(s) received by "
                                                         "current (logged-in) user")

    add_accept_op_parser.add_argument('--id',
                                       type=str,
                                       metavar='<request_id>',
                                       required=True,
                                       help='Id of the sharing request'
                                       '\nYou can use {list_requests} command to list pending request(s)')

    add_accept_op_parser.set_defaults(func=node_sharing_ops, parser=add_accept_op_parser)

    # Decline sharing request
    add_decline_op_parser = sharing_subparser.add_parser('decline',
                                                         help='Decline sharing request(s)',
                                                         formatter_class=argparse.RawTextHelpFormatter,
                                                         description="Decline request to share node(s) received by "
                                                         "current (logged-in) user")

    add_decline_op_parser.add_argument('--id',
                                       type=str,
                                       metavar='<request_id>',
                                       required=True,
                                       help='Id of the sharing request'
                                       '\nYou can use {list_requests} command to list pending request(s)')
    
    add_decline_op_parser.set_defaults(func=node_sharing_ops, parser=add_decline_op_parser)

    # Cancel pending requests
    cancel_request_op_parser = sharing_subparser.add_parser('cancel',
                                                            help='Cancel sharing request(s)',
                                                            formatter_class=argparse.RawTextHelpFormatter,
                                                            description='Cancel request to share node(s) '
                                                            'sent by current (logged-in) user')

    cancel_request_op_parser.add_argument('--id',
                                            type=str,
                                            metavar='<request_id>',
                                            help='Id of the sharing request\nYou can use {list_requests} command to list pending request(s)',
                                            required=True)

    cancel_request_op_parser.set_defaults(func=node_sharing_ops, parser=cancel_request_op_parser)

    # List sharing details for node(s) associated with user
    list_nodes_op_parser = sharing_subparser.add_parser('list_nodes',
                                                        help='List node(s) sharing details',
                                                        formatter_class=argparse.RawTextHelpFormatter,
                                                        description='Get sharing details of node(s) associated with current (logged-in) user'
                                                        )

    list_nodes_op_parser.add_argument('--node',
                                     type=str,
                                     metavar='<node_id>',
                                     help='Node Id of the node.\nIf provided, will list sharing details of a particular node'
                                     '\nDefault: List details of all node(s)')

    list_nodes_op_parser.set_defaults(func=node_sharing_ops, parser=list_nodes_op_parser)

    # List details of sharing request(s)
    list_request_op_parser = sharing_subparser.add_parser('list_requests',
                                                          help='List pending request(s)',
                                                          formatter_class=argparse.RawTextHelpFormatter,
                                                          description='Get details of pending request(s) ',
                                                          epilog="primary user:\n\tGet details of pending request(s) "
                                                          "sent by current (logged-in) user"
                                                          "\nsecondary user:\n\tGet details of pending request(s) "
                                                          "received by current (logged-in) user"
                                                          )

    list_request_op_parser.add_argument('--primary_user',
                                       action='store_true',
                                       help='If provided, current (logged-in) user is set as primary user\n'
                                            'Default: User is set as secondary user')

    list_request_op_parser.add_argument('--id',
                                       type=str,
                                       metavar='<request_id>',
                                       help='Id of the sharing request\nIf provided, will list details of a particular request'
                                       '\nDefault: List details of all request(s)')

    list_request_op_parser.set_defaults(func=node_sharing_ops, parser=list_request_op_parser)

    # Set parsers to print help for associated commands
    PARSER_HELP_PRINT = {
        'sharing_ops': sharing_parser,
        'add_user': add_op_parser,
        'accept': add_accept_op_parser,
        'decline': add_decline_op_parser,
        'cancel': cancel_request_op_parser,
        'remove_user': remove_user_op_parser,
        'list_nodes': list_nodes_op_parser,
        'list_requests': list_request_op_parser
        }

    args = parser.parse_args()

    if args.func is not None:
        try:
            args.func(vars=vars(args))
        except KeyboardInterrupt:
            log.debug('KeyboardInterrupt occurred. Login session is aborted.')
            print("\nExiting...")
        except Exception as err:
            log.error(err)
    else:
        parser.print_help()


if __name__ == '__main__':
    main()
