from Opcode import Opcode
from State import State

class Node:

    def __init__(self, tag: int, opcodes: [Opcode]):
        self.tag = tag
        self.opcodes = opcodes
        self.state = State()
    
    def __str__(self) -> str:
        return '%s' % self.tag

    def __repr__(self) -> str:
        return '<%s object> %s' % (self.__class__.__name__, self.tag)

    def __eq__(self, other):
        return self.tag == other.tag

    def set_state(self, state: State):
        self.state = state