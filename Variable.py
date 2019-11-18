from z3 import *

class Variable:

    def __init__(self, name: str, value: str, z3_var: BitVecRef):
        self.name = name
        self.value = value.replace('\n', '').replace(' ', '')
        self.z3_var = z3_var

    def __str__(self) -> str:
        return (self.name, self.value)

    def __repr__(self) -> str:
        return '<%s object> (%s, %s)' % (self.__class__.__name__, self.name, self.value)

class Variables:

    def __init__(self):
        self.variables = list()
        self.variable_mapping = dict()

    def __str__(self) -> str:
        return self.variables

    def __repr__(self) -> str:
        return '<%s object> %s' % (self.__class__.__name__, self.variables)

    def get_variable(self, variable: Variable) -> BitVecRef:
        for v in self.variables:
            if variable.value == v.value:
                self.variable_mapping[variable.name] = v.name
                return v.z3_var
        self.variables.append(variable)
        return variable.z3_var