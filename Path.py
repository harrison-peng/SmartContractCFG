from Node import Node
from PathConstraint import PathConstraint

class Path:

    def __init__(self):
        self.path = list()
        self.path_constraint = list()
        self.gas = 0

    def add_node(self, node: Node):
        self.path.append(node)

    def add_path_constraints(self, constraints: [PathConstraint]):
        slef.path_constraint += constraints

    def count_specific_node_num(self, tag: int) -> int:
        return len([node for node in self.path if node.tag == tag])