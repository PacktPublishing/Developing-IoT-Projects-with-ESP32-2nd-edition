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

CLAIM_INITIATE_SUFFIX = "claim/initiate"
CLAIM_VERIFY_SUFFIX = "claim/verify"

claim_base_url = "https://esp-claiming.rainmaker.espressif.com/"
claim_initiate_url = claim_base_url + CLAIM_INITIATE_SUFFIX
claim_verify_url = claim_base_url + CLAIM_VERIFY_SUFFIX

def claim_config_get_base_url():
    return claim_base_url

def claim_config_get_initiate_url():
    return claim_initiate_url

def claim_config_get_verify_url():
    return claim_verify_url

def claim_config_set_base_url(base_url):
    global claim_base_url, claim_initiate_url, claim_verify_url
    claim_base_url = base_url
    claim_initiate_url = claim_base_url + CLAIM_INITIATE_SUFFIX
    claim_verify_url = claim_base_url + CLAIM_VERIFY_SUFFIX
    print('Setting claim base URL: ' + claim_base_url)
