import var_generator


def init():
    global FINAL_PC_GAS
    FINAL_PC_GAS = []

    global gen
    gen = var_generator.Generator()

    global FINAL_GAS_SUM
    FINAL_GAS_SUM = dict()


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
