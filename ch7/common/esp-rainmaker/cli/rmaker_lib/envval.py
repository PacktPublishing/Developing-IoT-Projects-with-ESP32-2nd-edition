import os
from rmaker_lib.constants import HOME_DIRECTORY


# environment variables
RM_USER_CONFIG_DIR = 'RM_USER_CONFIG_DIR'
RM_CLI_OUTDIR = 'RM_CLI_OUTDIR'

DEFAULT_RM_USER_CONFIG_DIR = HOME_DIRECTORY+'.espressif/rainmaker'
DEFAULT_RM_CLI_OUT_DIR = HOME_DIRECTORY+'.espressif/rainmaker/claim_data'

def get_rm_user_config_dir():
    config_dir = os.getenv(RM_USER_CONFIG_DIR, DEFAULT_RM_USER_CONFIG_DIR)
    config_dir = os.path.expanduser(config_dir)
    return config_dir

def get_rm_cli_outdir():
    rm_cli_outdir = os.getenv(RM_CLI_OUTDIR, DEFAULT_RM_CLI_OUT_DIR)
    rm_cli_outdir = os.path.join(os.path.expanduser(rm_cli_outdir))
    return rm_cli_outdir