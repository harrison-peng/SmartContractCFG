from z3 import *
from Node import Node

class Path:

    def __init__(self):
        self.path = list()
        self.path_constraint = list()
        self.gas = 0
        self.solver = Solver()

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
        return self.solver.check() == sat

    def model(self):
        return self.solver.model()

    def solve_max_gas(self, gas: int) -> int:
        self.solver.push()
        self.solver.add(self.gas > gas)
        while self.solver.check() == sat:
            gas += 10000
            self.solver.pop()
            self.solver.push()
            self.solver.add(self.gas > gas)
