import logging
from Variable import Variables

logging.basicConfig(format='[%(levelname)s]: %(message)s', level=logging.DEBUG)

# NOTE: ANALYSIS OPTIONS

# NOTE: Detect loop once and evaluate to n
LOOP_DETECTION = False

# NOTE: How many times to execute the loop if not detecting the loop
LOOP_ITERATIONS = 3
MAX_LOOP_ITERATIONS = 2

# NOTE: Execute the loop in attack synthesis
ATTACK_SYNTHESIS_EXECUTE_LOOP = False

# NOTE: Set the model value ourselves instead he z3 model value
SET_MODEL_VALUE = False

# NOTE: Model value
MODEL_VALUE = {'Id_000235': 100000, 'Id_000439': 100000}

# NOTE: CONSTANT

UNSIGNED_BOUND_NUMBER = 2**256 - 1

ADDRESS_BOUND_NUMBER = 2**160

BYTE_BOUND_NUMBER = 32

EDGE_COLOR = {'blue': 'green', 'green': 'purple', 'purple': 'red', 'red': 'black', 'black': 'black'}

PATHS = list()

VARIABLES = Variables()