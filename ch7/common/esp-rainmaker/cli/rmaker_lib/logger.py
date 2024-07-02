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
import logging
from logging import handlers
from datetime import datetime

log_base_path = os.path.dirname(os.path.dirname(__file__))
log_dir_path = os.path.join(log_base_path, 'logs')

if not os.path.exists(log_dir_path):
    os.makedirs(log_dir_path)

date_time_obj = datetime.now()
log_filename = os.path.join(log_dir_path, "rmaker_cli_" + date_time_obj.strftime("%Y-%m-%d") + ".log")

log = logging.getLogger("CLI_LOGS")
file_formatter = logging.Formatter('%(asctime)s:[%(funcName)s]:\
[%(levelname)s]:%(message)s')
console_formatter = logging.Formatter('[%(levelname)s]:%(message)s')
log.setLevel(logging.DEBUG)

console_handler = logging.StreamHandler()
console_handler.setLevel(logging.ERROR)
console_handler.setFormatter(console_formatter)

file_handler = handlers.RotatingFileHandler(log_filename,
                                            maxBytes=1024 * 1024,
                                            backupCount=300)
file_handler.setFormatter(file_formatter)
file_handler.setLevel(logging.DEBUG)

log.addHandler(file_handler)
log.addHandler(console_handler)
