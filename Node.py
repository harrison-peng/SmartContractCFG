from Opcode import Opcode

class Node:

    def __init__(self, tag: int, opcodes: [Opcode]):
        self.tag = tag
        self.opcodes = opcodes
    
    def __str__(self) -> str:
        return '%s' % self.tag

    def __repr__(self) -> str:
        return '<%s object> %s' % (self.__class__.__name__, self.tag)

    def __eq__(self, other):
        return self.tag == other.tag