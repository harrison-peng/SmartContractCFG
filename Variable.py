from z3 import *

class Variable:

    def __init__(self, name: str, value: str, z3_var: BitVecRef):
        self.name = name
        self.value = value
        self.z3_var = z3_var

    def __str__(self) -> str:
        return (self.name, self.value)

    def __repr__(self) -> str:
        return '<%s object> (%s, %s)' % (self.__class__.__name__, self.name, self.value)

class Variables:

    def __init__(self):
        self.variables = list()

    def __str__(self) -> str:
        return self.variables

    def __repr__(self) -> str:
        return '<%s object> %s' % (self.__class__.__name__, self.variables)

    def add_variable(self, variable: Variable):
        self.variables.append(variable)

    def get_z3_var_by_value(self, value: str) -> BitVecRef:
        z3_vars = [variable.z3_var for variable in self.variables if variable.value == value]
        if len(z3_vars) == 0:
            return None
        else:
            return z3_vars[0]