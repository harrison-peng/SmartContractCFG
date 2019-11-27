import os
import logging
from Variable import Variables

# NOTE: Log Setting
logging.basicConfig(format='[%(levelname)s]: %(message)s', level=logging.DEBUG)

# NOTE: Global Constants
UNSIGNED_BOUND_NUMBER = 2**256 - 1
ADDRESS_BOUND_NUMBER = 2**160
BYTE_BOUND_NUMBER = 32
ROOT_PATH = os.path.dirname(__file__)


# NOTE: Settings
# Detect loop once and evaluate to n
LOOP_DETECTION = True
# How many times to execute the loop if not detecting the loop
MAX_LOOP_ITERATIONS = 2
# Set the model value ourselves instead he z3 model value
SET_MODEL_VALUE = False
# Remove Unreached node
REMOVE_UNREACHED_NODE = False
# CFG format
CFG_FORMAT = None
# contain state information in CFG
CFG_STATE = False
# Solver Timeout (millisecond)
TIMEOUT = 2000
# Output Path
OUTPUT_PATH = os.path.join(ROOT_PATH, 'result')