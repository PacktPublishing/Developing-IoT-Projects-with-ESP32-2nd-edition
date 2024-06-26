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

import os
from os import path
from pathlib import Path
from io import StringIO
import sys
from sys import exit
import time
import re
import requests
import json
import binascii
from types import SimpleNamespace
from rmaker_lib.constants import DOT_CRT, DOT_CSV, DOT_INFO, DOT_KEY, ENDPOINT, NODE, NODE_INFO, HOST
from rmaker_lib.logger import log
from cryptography import x509
from cryptography.x509.oid import NameOID
from cryptography.hazmat.primitives import hashes, hmac, serialization
from cryptography.hazmat.backends import default_backend
from cryptography.hazmat.primitives.serialization import load_pem_private_key
from cryptography.hazmat.primitives.asymmetric import rsa, ec
from rmaker_tools.rmaker_claim.claim_config import claim_config_get_initiate_url, claim_config_get_verify_url
from rmaker_lib import session, configmanager
from rmaker_lib.exceptions import SSLError
from rmaker_cmd import node
from rmaker_lib.envval import get_rm_cli_outdir
import esptool
from esp_secure_cert.tlv_format import tlv_priv_key_t, tlv_priv_key_type_t, generate_partition_no_ds

if os.getenv('IDF_PATH'):
    sys.path.insert(0, os.path.join(os.getenv('IDF_PATH'),
                                    'components',
                                    'nvs_flash',
                                    'nvs_partition_generator'))
    import nvs_partition_gen
else:
    log.error("Please set the IDF_PATH environment variable.")
    exit(0)

CURR_DIR = os.path.dirname(__file__)
CERT_FILE = os.path.abspath(os.path.join(CURR_DIR, os.pardir, os.pardir, 'server_cert/server_cert.pem'))

CERT_VENDOR_ID = 0x131B
CERT_PRODUCT_ID = 0x2

RM_CLI_OUTPUT_DIR = get_rm_cli_outdir()

secure_cert_partition_flash_address = '0xD000'

# List of efuse blocks
#
# Name, Index, Read Address, Read Protect Bit, Write Protect Bit
BLOCKS = [
    ("BLOCK_SYS_DATA", 2, 0x3f41a05c, None, 21)
]


def flash_nvs_partition_bin(port, bin_to_flash, address):
    """
    Flash binary onto node

    :param port: Serial Port
    :type port: str

    :param bin_to_flash: Filname of binary to flash
    :type bin_to_flash: str

    :raises Exception: If there is any issue when flashing binary onto node

    :return: None on Success
    :rtype: None
    """
    try:
        if not port:
            sys.exit("If you want to write the claim data to flash, please provide the <port> argument.")
        print("Flashing binary onto node")
        log.info("Flashing binary onto node")
        command = ['--port', port, 'write_flash', address, bin_to_flash]
        esptool.main(command)
    except Exception as err:
        log.error(err)
        sys.exit(1)


def get_node_mac(port):
    """
    Get MAC Address from device

    :param port: Serial Port
    :type port: str

    :return: MAC Address on Success
    :rtype: str
    """
    if not port:
        sys.exit("<port> argument not provided. Cannot read MAC address from node.")
    command = ['--port', port, 'chip_id']
    log.info("Running esptool command to get mac from device")

    try:
        sys.stdout = mystdout = StringIO()
        esptool.main(command)
        sys.stdout = sys.__stdout__

    except esptool.FatalError:
        sys.stdout = sys.__stdout__
        log.debug(sys.stdout)
        log.error('MAC could not be autodetected. Please provide by using --mac argument of claim command.')
        sys.exit(0)

    # Finds the first occurence of the line
    # with the MAC Address from the output.
    mac = next(filter(lambda line: 'MAC: ' in line,
                      mystdout.getvalue().splitlines()))
    mac_addr = mac.split('MAC: ')[1].replace(':', '').upper()
    log.debug("MAC address received: " + mac_addr)
    return mac_addr

def gen_host_csr(private_key, common_name, subjectPairs: dict = {}):
    """
    Generate Host CSR

    :param private_key: RSA Private Key to sign CSR
    :type private_key: RSA Key Object

    :param common_name: Common Name used in subject name of certificate,
                        defaults to None
    :type common_name: str|None

    :param subjectPairs: Ordered Key-Value pairs that will go into CSR's subject
    :type subjectPairs: dict[str, str]

    :return: CSR on Success, None on Failure
    :rtype: str|None
    """
    # Generate CSR on host
    builder = x509.CertificateSigningRequestBuilder()
    # Generate CSR subject
    subjectNameAttributes = [x509.NameAttribute(NameOID.COMMON_NAME, common_name)]
    for key, value in subjectPairs.items():
        subjectNameAttributes.append(x509.NameAttribute(x509.ObjectIdentifier(key), value))
    builder = builder.subject_name(x509.Name(subjectNameAttributes))
    builder = builder.add_extension(
        x509.BasicConstraints(ca=False, path_length=None), critical=True,
    )
    request = builder.sign(
        private_key, hashes.SHA256(), default_backend()
    )
    if isinstance(request, x509.CertificateSigningRequest) is not True:
        print("Certificate Signing Request could not be created")
        return None

    csr = request.public_bytes(serialization.Encoding.PEM).decode("utf-8")
    return csr


def gen_hex_str(octets=64):
    """
    Generate random hex string, it is used as PoP

    :param octets: Number of octets in random hex string, length is (octets * 2)
                    defaults to 4,
    :type: octets: int

    :return: random hex string on Success, None on Failure
    :rtype: str|None
    """
    # Generate random hex string
    return binascii.b2a_hex(os.urandom(octets)).decode()


def save_random_hex_str(dest_filedir, hex_str):
    """
    Create file for random hex string and update node_info.csv

    :param dest_filedir: Destination File Directory
    :type dest_filedir: str

    :param hex_str: Random hex string to write
    :type hex_str: str

    :raises Exception: If there is any issue when writing to file

    :return: None on Success
    :rtype: None
    """
    try:
        log.debug("Writing random hex string at location: " +
                  dest_filedir + 'random.info')
        with open(dest_filedir + 'random.info', 'w+') as info_file:
            info_file.write(hex_str)

        with open(dest_filedir + 'node_info.csv', 'a') as info_file:
            info_file.write('random,file,hex2bin,' +
                            dest_filedir + 'random.info')
            info_file.write('\n')
    except Exception as err:
        log.error(err)

def convert_private_key_from_pem_to_der(pem_file, out_der_file):
    with open(pem_file, 'rb') as f:
        pem_data = f.read()

    pem_key = load_pem_private_key(pem_data, None, default_backend())

    der_key = pem_key.private_bytes(
        encoding=serialization.Encoding.DER,
        format=serialization.PrivateFormat.TraditionalOpenSSL,
        encryption_algorithm=serialization.NoEncryption(),
    )

    with open(out_der_file, 'wb') as f:
        f.write(der_key)

def save_claim_data(dest_filedir, node_id, private_key, node_cert, endpointinfo, node_info_csv):
    """
    Create files with claiming details

    :param dest_filedir: Destination File Directory
    :type dest_filedir: str

    :param node_id: Node Id (data) to write to `node.info` file
    :type node_id: str

    :param private_key: Private Key (object) to write to `node.key` file
    :type private_key: bytes

    :param node_cert: Node Certificate (data) to write to `node.crt` file
    :type node_cert: str

    :param endpointinfo: MQTT endpoint (data) to write to `endpoint.info` file
    :type endpointinfo: str

    :param hex_str: random hex string
    :type hex_str: str

    :param node_info_csv: List of output csv file details (node information)
                          to write to `node_info.csv` file
    :type node_info_csv: list

    :raises Exception: If there is any issue when writing to file

    :return: None on Success
    :rtype: None
    """
    # Create files of each claim data info
    print("\nSaving claiming data info at location: ", dest_filedir)
    log.debug("Saving claiming data info at location: " +
              dest_filedir)
    try:
        log.debug("Writing node info at location: " +
                  dest_filedir + NODE+DOT_INFO)
        # Create files for each claim data - node info, node key,
        # node cert, endpoint info
        with open(dest_filedir+NODE+DOT_INFO, 'w+') as info_file:
            info_file.write(node_id)

        log.debug("Writing node info at location: " +
                  dest_filedir + NODE + DOT_KEY)
        with open(dest_filedir + NODE + DOT_KEY, 'wb+') as info_file:
            info_file.write(private_key)

        log.debug("Writing node info at location: " +
                  dest_filedir + NODE + DOT_CRT)
        with open(dest_filedir + NODE + DOT_CRT, 'w+') as info_file:
            info_file.write(node_cert)

        log.debug("Writing node info at location: " +
                  dest_filedir + ENDPOINT + DOT_INFO)
        with open(dest_filedir + ENDPOINT + DOT_INFO, 'w+') as info_file:
            info_file.write(endpointinfo)

        log.debug("Writing node info at location: " +
                  dest_filedir + NODE_INFO + DOT_CSV)

        with open(dest_filedir + NODE_INFO + DOT_CSV, 'w+') as info_file:
            for input_line in node_info_csv:
                info_file.write(input_line)
                info_file.write("\n")
    except Exception as file_error:
        raise file_error


def gen_nvs_partition_bin(dest_filedir, output_bin_filename):
    # Generate nvs args to be sent to NVS Partition Utility
    nvs_args = SimpleNamespace(input=dest_filedir+'node_info.csv',
                               output=output_bin_filename,
                               size='0x6000',
                               outdir=dest_filedir,
                               version=2)
    # Run NVS Partition Utility to create binary of node info data
    print("\nGenerating NVS Partition Binary from claiming data: " +
          dest_filedir + output_bin_filename)
    log.debug("Generating NVS Partition Binary from claiming data: " +
              dest_filedir + output_bin_filename)
    nvs_partition_gen.generate(nvs_args)


def set_claim_verify_data(claim_init_resp, private_key, matter):
    # Generate CSR with common_name=node_id received in response
    node_id = str(json.loads(
        claim_init_resp.text)['node_id'])
    print("Generating CSR")
    log.info("Generating CSR")
    subjectPairs = {}
    if matter:
        # Generate CSR
        # CHIP OID for vendor id
        VENDOR_ID = '1.3.6.1.4.1.37244.2.1'
        # CHIP OID for product id
        PRODUCT_ID = '1.3.6.1.4.1.37244.2.2'
        subjectPairs={
            VENDOR_ID:hex(CERT_VENDOR_ID)[2:].upper().zfill(4),
            PRODUCT_ID:hex(CERT_PRODUCT_ID)[2:].upper().zfill(4)
        }
    csr = gen_host_csr(private_key, common_name=node_id, subjectPairs=subjectPairs)
    if not csr:
        raise Exception("CSR Not Generated. Claiming Failed")
    log.info("CSR generated")
    claim_verify_data = {"csr": csr}
    # Save node id as node info to use while saving claim data
    # in csv file
    node_info = node_id
    return claim_verify_data, node_info


def set_claim_initiate_data(mac_addr, node_platform):
    # Set Claim initiate request data
    claim_initiate_data = {"mac_addr": mac_addr, "platform": node_platform}
    claim_init_enc_data = str(claim_initiate_data).replace(
        "'", '"')
    return claim_init_enc_data


def claim_verify(claim_verify_data, matter=False, header=None):
    if header is None:
        header = session.Session().request_header
    claim_verify_url = claim_config_get_verify_url()
    claim_verify_enc_data = str(claim_verify_data).replace(
        "'", '"')
    # TODO: Remove the 'test' param after claiming API deprecates it
    params = {"matter": matter, "test": True}
    log.debug("Claim Verify POST Request: url: " + claim_verify_url +
              " data: " + str(claim_verify_enc_data) + " headers: " +
              str(header) + " params: " + str(params) + " verify: " + CERT_FILE)
    claim_verify_response = requests.post(url=claim_verify_url,
                                          data=claim_verify_enc_data,
                                          params=params,
                                          headers=header,
                                          verify=CERT_FILE)
    if claim_verify_response.status_code != 200:
        log.error('Claim verification failed.\n' +
                  claim_verify_response.text)
        exit(0)
    print("Claim verify done")
    log.debug("Claim Verify POST Response: status code: " +
              str(claim_verify_response.status_code) +
              " and response text: " + claim_verify_response.text)
    log.info("Claim verify done")
    return claim_verify_response


def claim_initiate(claim_init_data, header=None):
    print("Claim initiate started")
    claim_initiate_url = claim_config_get_initiate_url()
    if header is None:
        header = session.Session().request_header
    try:
        # Claim Initiate Request
        log.info("Claim initiate started. Sending claim/initiate POST request")
        log.debug("Claim Initiate POST Request: url: " +
                  claim_initiate_url + " data: " +
                  str(claim_init_data) +
                  " headers: " + str(header) +
                  " verify: " + CERT_FILE)
        claim_initiate_response = requests.post(url=claim_initiate_url,
                                                data=claim_init_data,
                                                headers=header,
                                                verify=CERT_FILE)
        if claim_initiate_response.status_code != 200:
            log.error("Claim initiate failed.\n" +
                      claim_initiate_response.text)
            exit(0)
        print("Claim initiate done")
        log.debug("Claim Initiate POST Response: status code: " +
                  str(claim_initiate_response.status_code) +
                  " and response text: " + claim_initiate_response.text)
        log.info("Claim initiate done")
        return claim_initiate_response
    except requests.exceptions.SSLError:
        raise SSLError
    except requests.ConnectionError:
        log.error("Please check the Internet connection.")
        exit(0)


def start_claim_process(mac_addr, node_platform, private_key, matter=False):
    log.info("Creating session")
    try:
        # Set claim initiate data
        claim_init_data = set_claim_initiate_data(mac_addr, node_platform)

        # Perform claim initiate request
        claim_init_resp = claim_initiate(claim_init_data)

        # Set claim verify data
        claim_verify_data, node_info = set_claim_verify_data(claim_init_resp, private_key, matter)

        # Perform claim verify request
        claim_verify_resp = claim_verify(claim_verify_data, matter)

        # Get certificate from claim verify response
        node_cert = json.loads(claim_verify_resp.text)['certificate']
        print("Claim certificate received")
        log.info("Claim certificate received")

        return node_info, node_cert
    except requests.exceptions.SSLError:
        raise SSLError
    except requests.ConnectionError:
        log.error("Please check the Internet connection.")
        exit(0)


def generate_private_key():
    # Generate Key
    log.info("Generate RSA key")
    private_key = rsa.generate_private_key(
        public_exponent=65537,
        key_size=2048,
        backend=default_backend()
    )
    log.info("RSA Private Key generated")
    # Extract private key in bytes from private key object generated
    log.info("Extracting private key in bytes")
    private_key_bytes = private_key.private_bytes(
        encoding=serialization.Encoding.PEM,
        format=serialization.PrivateFormat.TraditionalOpenSSL,
        encryption_algorithm=serialization.NoEncryption())
    return private_key, private_key_bytes


def generate_private_ecc_key():
    # Generate Key
    log.info("Generate EC key")
    private_key = ec.generate_private_key(ec.SECP256R1(), default_backend())
    log.info("EC Private Key generated")
    # Extract private key in bytes from private key object generated
    log.info("Extracting private key in bytes")
    private_key_bytes = private_key.private_bytes(
        encoding=serialization.Encoding.PEM,
        format=serialization.PrivateFormat.PKCS8,
        encryption_algorithm=serialization.NoEncryption())
    return private_key, private_key_bytes

def verify_mac_dir_exists(creds_dir, mac_addr):
    mac_dir = Path(path.expanduser(str(creds_dir) + '/' + mac_addr))
    if mac_dir.exists():
        dest_filedir = str(mac_dir) + '/'
        output_bin_filename = mac_addr + '.bin'
        return dest_filedir, output_bin_filename
    return False, False


def create_mac_dir(creds_dir, mac_addr):
    # Create MAC directory
    mac_dir = Path(path.expanduser(str(creds_dir) + '/' + mac_addr))
    os.makedirs(path.expanduser(mac_dir))
    log.debug("Creating new directory " + str(mac_dir))
    output_bin_filename = mac_addr + '.bin'
    dest_filedir = str(mac_dir) + '/'
    return dest_filedir, output_bin_filename


def create_config_dir():
    config = configmanager.Config()
    userid = config.get_user_id()
    creds_dir = Path(os.path.join(RM_CLI_OUTPUT_DIR, userid))

    if not creds_dir.exists():
        os.makedirs(path.expanduser(creds_dir))
        log.debug("Creating new directory " + str(creds_dir))
    return userid, creds_dir


def get_mqtt_endpoint():
    # Set node claim data
    sys.stdout = StringIO()
    log.info("Getting MQTT Host")
    endpointinfo = node.get_mqtt_host(None)
    log.debug("Endpoint info received: " + endpointinfo)
    sys.stdout = sys.__stdout__
    return endpointinfo


def verify_claim_data_binary_exists(userid, mac_addr, dest_filedir, output_bin_filename):
    # Set config mac addr path
    mac_addr_config_path = os.path.join(RM_CLI_OUTPUT_DIR, userid, mac_addr, output_bin_filename)
    # Check if claim data for node exists in CONFIG directory
    log.debug("Checking if claim data for node exists in directory: " +
              RM_CLI_OUTPUT_DIR)
    curr_claim_data = configmanager.Config().get_binary_config(
        config_file=mac_addr_config_path)
    if curr_claim_data:
        print("\nClaiming data already exists at location: " +
              dest_filedir)
        log.debug("Claiming data already exists at location: " +
                  dest_filedir)
        return True
    return False


def verify_key_data_exists(key, file_name):
    """
    Verify if an entry for the given key exists in the NVS CSV file

    :param key: key to search in csv file
    :type key: str

    :param file_name: csv file name
    :type file_name: str

    :raises Exception: If there is any issue when reading file

    :return: True|False
    :rtype: Boolean
    """
    try:
        with open(file_name, 'r') as file:
            lines = file.readlines()
            for line in lines:
                row = [r.strip() for r in line.split(',')]
                if row[0] == key:
                    # row[3] has file name
                    with open(row[3], 'r') as rfile:
                        if rfile.read():
                            return True
            return False
    except Exception as file_error:
        raise file_error


def flash_existing_data(port, bin_to_flash, address):
    # Flashing existing binary onto node
    if not port:
        sys.exit("If you want to write the claim data to flash, please provide the <port> argument.")
    log.info("Using existing claiming data")
    print("Using existing claiming data")
    flash_nvs_partition_bin(port, bin_to_flash, address)
    log.info("Binary flashed onto node")


def set_csv_file_data(dest_filedir):
    # Set csv file data
    node_info_csv = [
        'key,type,encoding,value',
        'rmaker_creds,namespace,,',
        'node_id,file,binary,' +
        dest_filedir + 'node.info',
        'mqtt_host,file,binary,' +
        dest_filedir + 'endpoint.info',
        'client_cert,file,binary,' +
        dest_filedir + 'node.crt',
        'client_key,file,binary,' +
        dest_filedir + 'node.key'
    ]
    return node_info_csv

def split_device_cert(device_cert: str) -> tuple:
    """
    In case of matter claiming, claim_verify API returns device_cert and ca_cert in one string
    This function splits them separate

    :param device_cert: device_cert and ca_cert strings concatenated back-to-back
    :type device_cert: str

    :return: device_cert and ca_cert
    :rtype: tuple[str, str]
    """
    indices = [index for index in range(len(device_cert)) if device_cert[index:].startswith("-----BEGIN CERTIFICATE-----")]
    if len(indices) > 1:
        split_device_cert = device_cert[:indices[1]]
        split_ca_cert = device_cert[indices[1]:]
    else:
        split_device_cert = device_cert
        split_ca_cert = ""
    return split_device_cert, split_ca_cert

def qr_code_generate_image(qr_code, path):
    qr_code_payload = pyqrcode.create(qr_code)
    qr_code_payload.png(os.path.join(path, 'qr_code.png'), scale=6)
    qr_code_payload.show()

def add_matter_data_to_files(path, vendor_id, product_id):
    with open(OUT_FILE['mcsv'], 'r') as csv_file:
        csv_dict = csv.DictReader(csv_file)
        for row in csv_dict:
            with open(os.path.join(path, 'discriminator.info'), 'w+') as info_file:
                info_file.write(row['discriminator'])
            with open(os.path.join(path, 'iteration_count.info'), 'w+') as info_file:
                info_file.write(row['iteration-count'])
            with open(os.path.join(path, 'salt.info'), 'w+') as info_file:
                info_file.write(row['salt'])
            with open(os.path.join(path, 'verifier.info'), 'w+') as info_file:
                info_file.write(row['verifier'])
            with open(os.path.join(path, 'serial_num.info'), 'w+') as info_file:
                info_file.write(row['serial-num'])

    with open(os.path.join(path, 'vendor_id.info'), 'w+') as info_file:
        info_file.write(str(vendor_id))
    with open(os.path.join(path, 'product_id.info'), 'w+') as info_file:
        info_file.write(str(product_id))

    qr_code = None
    manual_code = None
    passcode = None
    with open(os.path.join(path, '-onb_codes.csv'), 'r') as info_file:
        csv_data = csv.DictReader(info_file)
        row = csv_data.__next__()
        qr_code = row['qrcode']
        manual_code = row['manualcode']
        passcode = row['passcode']

    with open(os.path.join(path, 'qr_code.info'), 'w+') as info_file:
        info_file.write(qr_code)
    with open(os.path.join(path, 'manual_code.info'), 'w+') as info_file:
        info_file.write(manual_code)
    with open(os.path.join(path, 'passcode.info'), 'w+') as info_file:
        info_file.write(passcode)

    print("QR code is: " + qr_code)
    print("Manual code is: " + manual_code)
    print("QR code URL: https://project-chip.github.io/connectedhomeip/qrcode.html?data=" + qr_code)

    os.rename(os.path.join(path, '-qrcode.png'), os.path.join(path, 'qr_code.png'))

    os.remove(os.path.join(path, '-onb_codes.csv'))
    shutil.rmtree(os.path.join(path, 'internal'))
    shutil.rmtree(os.path.join(path, 'staging'))
    qr_code_generate_image(qr_code, path)

def convert_x509_cert_from_pem_to_der(pem_file, out_der_file):
    with open(pem_file, 'rb') as f:
        pem_data = f.read()

    pem_cert = x509.load_pem_x509_certificate(pem_data, default_backend())
    der_cert = pem_cert.public_bytes(serialization.Encoding.DER)

    with open(out_der_file, 'wb') as f:
        f.write(der_cert)


def add_rainmaker_claim_data_to_files(path, device_cert, device_key, ca_cert):
    with open(os.path.join(path, 'device_cert.pem'), 'w+') as info_file:
        info_file.write(device_cert)
    with open(os.path.join(path, 'device_key.pem'), 'wb+') as info_file:
        info_file.write(device_key)
    with open(os.path.join(path, 'ca_cert.pem'), 'w+') as info_file:
        info_file.write(ca_cert)

    convert_x509_cert_from_pem_to_der(os.path.join(path, 'device_cert.pem'), os.path.join(path, 'device_cert.der'))
    convert_private_key_from_pem_to_der(os.path.join(path, 'device_key.pem'), os.path.join(path, 'device_key.der'))
    convert_x509_cert_from_pem_to_der(os.path.join(path, 'ca_cert.pem'), os.path.join(path, 'ca_cert.der'))

def gen_esp_secure_cert_partition_bin(path, esp_secure_cert_file_name, node_platform):
    tlv_priv_key = tlv_priv_key_t(tlv_priv_key_type_t.ESP_SECURE_CERT_DEFAULT_FORMAT_KEY, os.path.join(path, 'device_key.der'), None)
    generate_partition_no_ds(tlv_priv_key, os.path.join(path, 'device_cert.der'), os.path.join(path, 'ca_cert.der'), node_platform, os.path.join(path, esp_secure_cert_file_name))

def claim(port=None, node_platform=None, mac_addr=None, flash_address=None, matter=False, out_dir=None):
    """
    Claim the node connected to the given serial port
    (Get cloud credentials)

    :param port: Serial Port
    :type port: str

    :param mac_addr: MAC Addr
    :type mac_addr: str

    :param flash_address: Flash Address
    :type flash_address: str

    :raises Exception: If there is an HTTP issue while claiming
            SSLError: If there is an issue in SSL certificate validation
            ConnectionError: If there is network connection issue

    :return: None on Success
    :rtype: None
    """
    try:
        node_info = None
        private_key = None
        hex_str = None
        claim_data_binary_exists = False
        dest_filedir = None
        output_bin_filename = None

        if not flash_address:
            flash_address = '0x340000'

        if out_dir:
            global RM_CLI_OUTPUT_DIR
            RM_CLI_OUTPUT_DIR = out_dir

        # Create base config creds dir
        userid, creds_dir = create_config_dir()

        # Get mac addr if not provided
        if not mac_addr:
            mac_addr = get_node_mac(port)

        # use default platform if not passed
        if not node_platform:
            node_platform = HOST

        # Verify mac directory exists
        dest_filedir, output_bin_filename = verify_mac_dir_exists(creds_dir, mac_addr)

        # Create mac subdirectory in creds config directory created above
        if not dest_filedir and not output_bin_filename:
            dest_filedir, output_bin_filename = create_mac_dir(creds_dir, mac_addr)

        # Set NVS binary filename
        nvs_bin_filename = dest_filedir + output_bin_filename
        esp_secure_cert_file_name = 'esp_secure_cert.bin'

        # Set csv file output data
        node_info_csv = set_csv_file_data(dest_filedir)
        # Verify existing data exists
        claim_data_binary_exists = verify_claim_data_binary_exists(userid, mac_addr, dest_filedir, output_bin_filename)
        # If the device was previously claimed without --matter, this check would reclaim the device using matter claiming.
        if claim_data_binary_exists and not matter:
            # Check if random key exist in csv
            random_key_exist_in_csv = verify_key_data_exists('random', dest_filedir + NODE_INFO + DOT_CSV)
            if not random_key_exist_in_csv:
                # generate random key and add to csv
                print('Random data does not exist, Creating new nvs binary. It will change your Wi-Fi Provisioning Pin')
                log.info('Random data does not exist, Creating new nvs binary. It will change your Wi-Fi Provisioning Pin')
                hex_str = gen_hex_str()
                save_random_hex_str(dest_filedir, hex_str)
                gen_nvs_partition_bin(dest_filedir, output_bin_filename)
            # Flash NVS binary onto node
            flash_existing_data(port, nvs_bin_filename, flash_address)
            return

        start = time.time()

        # Generate private key
        if not matter:
            private_key, private_key_bytes = generate_private_key()
        else:
            private_key, private_key_bytes = generate_private_ecc_key()

        print("\nClaiming process started. This may take time.")
        log.info("Claiming process started. This may take time.")

        # Start claim process
        node_info, node_cert = start_claim_process(mac_addr, node_platform, private_key, matter)

        # Get MQTT endpoint
        endpointinfo = get_mqtt_endpoint()

        # Create output claim files

        # TODO: Use node-id and node-cert
        save_claim_data(dest_filedir, node_info, private_key_bytes, node_cert, endpointinfo, node_info_csv)

        print("Claiming done")
        log.info("Claiming done")
        print("Time(s):" + str(time.time() - start))
        if not matter:
            # Generate random hex string
            hex_str = gen_hex_str()

            save_random_hex_str(dest_filedir, hex_str)
            # Generate nvs partition binary
            gen_nvs_partition_bin(dest_filedir, output_bin_filename)

            # Flash generated NVS partition binary
            flash_nvs_partition_bin(port, nvs_bin_filename, flash_address)
        else:
            device_cert, ca_cert = split_device_cert(node_cert)
            add_rainmaker_claim_data_to_files(dest_filedir, device_cert, private_key_bytes, ca_cert)
            gen_esp_secure_cert_partition_bin(dest_filedir, esp_secure_cert_file_name, node_platform)
            print("Generated esp_secure_cert partition: " + str(os.path.join(dest_filedir, esp_secure_cert_file_name)))
            flash_nvs_partition_bin(port, os.path.join(dest_filedir, esp_secure_cert_file_name), secure_cert_partition_flash_address)
    except Exception as err:
        log.error(err)
        sys.exit(err)
