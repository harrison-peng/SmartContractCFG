class Opcode:

    def __init__(self, pc: int, name: str, value: int):
        self.name = name
        self.value = value
        self.pc = pc

    def __str__(self) -> str:
        return self.name

    def __repr__(self) -> str:
        if self.value:
            return '<%s object> %s: %s %s' % (self.__class__.__name__, self.pc, self.name, self.value)
        else:
            return '<%s object> %s: %s' % (self.__class__.__name__, self.pc, self.name)

    def get_next_pc(self) -> int:
        if self.name.startswith('PUSH', 0):
            return self.pc + 1 + int(self.name.split('PUSH')[1])
        else:
            return self.pc + 1