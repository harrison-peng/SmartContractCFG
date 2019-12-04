from z3 import *
from src.Opcode import Opcode
from src.State import State

class Node:

    def __init__(self, tag: int, opcodes: [Opcode]):
        self.tag = tag
        self.opcodes = opcodes
        self.state = State()
        self.gas = 0
        self.path_constraint = None
        self.color = 'black'
        self.visited = False
        self.count = 0
    
    def __str__(self) -> str:
        return '%s' % self.tag

    def __repr__(self) -> str:
        return '<%s object> %s' % (self.__class__.__name__, self.tag)

    def __eq__(self, other: 'Node') -> bool:
        return self.tag == other.tag

    def set_gas(self, gas: int) -> None:
        gas = int(gas.as_long()) if isinstance(gas, BitVecNumRef) else gas
        gas = int(gas) if isinstance(gas, float) else gas 
        self.gas = gas
    
    def set_path_constraint(self, constraint: ArithRef) -> None:
        self.path_constraint = constraint

    def set_state(self, state: State) -> None:
        self.state = state

    def set_color(self, color: str) -> None:
        self.color = color

    def visit(self) -> None:
        self.visited = True
        self.count += 1