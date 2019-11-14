from z3 import *

class Variable:

    def __init__(self, name: str, value: str, z3_var: BitVecRef):
        self.name = name
        self.value = value
        self.z3_var = z3_var

class Variables:

    def __init__(self):
        self.varialbes = list()

    def add_variable(self, variable: Varialbe):
        self.varialbes.append(variable)

    def get_z3_var_by_value(self, value: str) -> BitVecRef:
        z3_vars = [variable.z3_var for variable in Variables if Variable.value == value]
        if len(z3_vars) == 0:
            return None
        else:
            return z3_vars[0]