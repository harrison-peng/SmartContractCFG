from z3 import *
from Node import Node
from State import State

class Path:

    def __init__(self):
        self.path = list()
        self.path_constraint = list()
        self.gas = 0
        self.solver = Solver()
        self.model = None
        self.model_gas = None

    def __str__(self) -> str:
        return '%s' % self.path

    def __repr__(self) -> str:
        return '<%s object> %s' % (self.__class__.__name__, self.path)

    def add_node(self, node: Node):
        self.path.append(node)

    def add_path_constraints(self, constraints: list):
        self.path_constraint += constraints

    def count_specific_node_num(self, tag: int) -> int:
        return len([node for node in self.path if node.tag == tag])

    def add_gas(self, gas):
        self.gas += gas
        self.gas = simplify(self.gas) if is_expr(self.gas) else int(self.gas)

    def is_constant_gas(self) -> bool:
        self.gas = simplify(self.gas) if is_expr(self.gas) else int(self.gas)
        self.gas = int(self.gas.as_long) if isinstance(self.gas, BitVecNumRef) else self.gas
        self.gas = int(self.gas) if isinstance(self.gas, float) else self.gas
        return isinstance(self.gas, int)

    def solve(self):
        for contraint in self.path_constraint:
            self.solver.add(contraint)
        if self.solver.check() == sat:
            self.model = self.solver.model()
            return True
        return False

    def solve_max_gas(self, gas: int) -> int:
        self.solver.push()
        self.solver.add(self.gas > gas)
        while self.solver.check() == sat:
            gas += 5000
            self.solver.pop()
            self.solver.push()
            self.solver.add(self.gas > gas)
        self.solver.pop()
        self.solver.push()
        self.solver.add(self.gas > gas - 10000)
        if self.solver.check() == sat:
            self.model = self.solver.model()
        else:
            raise Error('Solver Error')

    def assign_model(self) -> int:
        gas = 0
        state = State()
        for node in self.path:
            for opcode in node.opcodes:
                gas += state.simulate_with_model(opcode, self.model)
        self.model_gas = gas