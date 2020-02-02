import os
import logging

# NOTE: Log Setting
logging.basicConfig(
    format='%(asctime)s [%(levelname)s]: %(message)s',
    datefmt='%y-%m-%d %H:%M',
    level=logging.INFO
)

# NOTE: Global Constants
UNSIGNED_BOUND_NUMBER = 2**256 - 1
ADDRESS_BOUND_NUMBER = 2**160
BYTE_BOUND_NUMBER = 32
ROOT_PATH = os.path.join(os.path.abspath(os.path.dirname(__file__)), os.pardir)


# NOTE: Settings
# Detect loop once and evaluate to n
LOOP_DETECTION = True
# How many times to execute the loop if not detecting the loop
MAX_LOOP_ITERATIONS = 5
# Set the model value ourselves instead he z3 model value
SET_MODEL_VALUE = False
# Remove Unreached node
REMOVE_UNREACHED_NODE = False
# CFG format
CFG_FORMAT = None
# contain state information in CFG
CFG_STATE = False
# Solver Timeout (millisecond)
TIMEOUT = 30000
# Output Path
OUTPUT_PATH = os.path.join(ROOT_PATH, 'result')
# LOOP DETECTION
DETECT_LOOP = False
# ADDRESS
ADDRESS = None
# Max Node Visited Times
ENABLE_MAX_NODE_VISITED_TIMES = True
MAX_NODE_VISITED_TIMES = 100
# SPECIFY SOLIDITY VERSION
SPECILIFY_SOL_VERSION = False