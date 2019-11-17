import logging
from Variable import Variables

# NOTE: Log Setting
logging.basicConfig(format='[%(levelname)s]: %(message)s', level=logging.DEBUG)

# NOTE: Global Constants
UNSIGNED_BOUND_NUMBER = 2**256 - 1
ADDRESS_BOUND_NUMBER = 2**160
BYTE_BOUND_NUMBER = 32

# NOTE: Settings
# Detect loop once and evaluate to n
LOOP_DETECTION = False
# How many times to execute the loop if not detecting the loop
LOOP_ITERATIONS = 3
MAX_LOOP_ITERATIONS = 2
# Execute the loop in attack synthesis
ATTACK_SYNTHESIS_EXECUTE_LOOP = False
# Set the model value ourselves instead he z3 model value
SET_MODEL_VALUE = False

EDGE_COLOR = {'blue': 'green', 'green': 'purple', 'purple': 'red', 'red': 'black', 'black': 'black'}

# NOTE: Global Variable
PATHS = list()
VARIABLES = Variables()

def init_path():
    PATHS = list()

def init_variables():
    VARIABLES = Variables()
