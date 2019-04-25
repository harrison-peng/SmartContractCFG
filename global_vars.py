import var_generator


def init():
    global FINAL_PC_GAS
    FINAL_PC_GAS = []

    global gen
    gen = var_generator.Generator()

    global FINAL_GAS_SUM
    FINAL_GAS_SUM = dict()

    global TOTAL_PATH_COUNT
    TOTAL_PATH_COUNT = 0

    global SAT_PATH_COUNT
    SAT_PATH_COUNT = 0

    global VAR_TABLE
    VAR_TABLE = dict()

    global UNSIGNED_BOUND_NUMBER
    UNSIGNED_BOUND_NUMBER = 2**256 - 1


def add_pc_gas(value):
    FINAL_PC_GAS.append(value)


def get_pc_gas():
    return FINAL_PC_GAS


def get_gen():
    return gen


def add_final_gas(tag, gas):
    if tag in FINAL_GAS_SUM.keys():
        FINAL_GAS_SUM[tag].append(gas)
    else:
        FINAL_GAS_SUM[tag] = [gas]


def get_final_gas():
    return FINAL_GAS_SUM


def add_total_path_count():
    global TOTAL_PATH_COUNT
    TOTAL_PATH_COUNT += 1


def get_total_path_count():
    return TOTAL_PATH_COUNT


def add_sat_path_count():
    global SAT_PATH_COUNT
    SAT_PATH_COUNT += 1


def get_sat_path_count():
    return SAT_PATH_COUNT


def add_var_table(key, val):
    VAR_TABLE[key] = val


def var_in_var_table(key):
    if key in VAR_TABLE.keys():
        return True
    else:
        return False


def get_var_table():
    return VAR_TABLE


def get_var_in_table(key):
    return VAR_TABLE[key]

