from z3 import *
from Node import Node
from PathConstraint import PathConstraint

class Path:

    def __init__(self):
        self.path = list()
        self.path_constraint = list()
        self.gas = 0

    def __str__(self) -> str:
        return '%s' % self.path

    def __repr__(self) -> str:
        return '<%s object> %s' % (self.__class__.__name__, self.path)

    def add_node(self, node: Node):
        self.path.append(node)

    def add_path_constraints(self, constraints: [PathConstraint]):
        self.path_constraint += constraints

    def count_specific_node_num(self, tag: int) -> int:
        return len([node for node in self.path if node.tag == tag])

    def add_gas(self, gas):
        self.gas += gas
        self.gas = simplify(self.gas) if is_expr(self.gas) else int(self.gas)

    def solve(self):
        solver = Solver()
        for contraint in self.path_constraint:
            solver.add(contraint)
        if solver.check() == sat:
            print(solver.model())
        else:
            print("UNSAT")