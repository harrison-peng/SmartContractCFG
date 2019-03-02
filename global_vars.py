def init():
    global FINAL_PC_GAS
    FINAL_PC_GAS = []


def add_pc_gas(value):
    FINAL_PC_GAS.append(value)


def get_pc_gas():
    return FINAL_PC_GAS
