from Variable import Variable

class SimularionResult:

    def __init__(self):
        self.gas = 0
        self.path_constraints = list()
        self.jump_condition = None
        self.jump_tag = None

    def add_path_constraint(self, constraint):
        self.path_constraints.append(constraint)
    
    def set_gas(self, gas: int):
        self.gas = gas

    def set_jump_tag(self, tag: int):
        self.jump_tag = tag

    def set_jump_condition(self, condition):
        self.jump_condition = condition