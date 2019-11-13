from Opcode import Opcode
from Path import Path
from SimulationResult import SimularionResult

class State:

    def __init__(self):
        self.stack = dict()
        self.memory = dict()
        self.storage = dict()
        self.gas = 0
        self.path = Path()

    def __deepcopy__(self, memo):
        cls = self.__class__
        result = cls.__new__(cls)
        memo[id(self)] = result
        for k, v in self.__dict__.items():
            setattr(result, k, deepcopy(v, memo))
        return result

    def set_gas(self, gas: int):
        self.gas = gas

    def simulate(self, opcode: Opcode) -> SimularionResult:
        # TODO: implement simulate state
        pass