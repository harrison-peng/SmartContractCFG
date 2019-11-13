from global_constants import logging, LOOP_DETECTION, LOOP_ITERATIONS
from Cfg import Cfg
from Opcode import Opcode
from Node import Node
from Edge import Edge
from State import State
from PathConstraints import PathConstraints
from Path import Path

class Analyzer:

    def __init__(self, cfg: Cfg):
        self.cfg = cfg
        self.state = State()
        self.path_constraints = PathConstraints()
        self.paths = list()

    def symbolic_execution(self, tag: int):
        node = cfg.get_node(tag)
        gas = 0

        for opcode in node.opcodes:
            # NOTE: state simulation
            result = state.simulate(opcode)
            self.path_constraints.add_constraints(result.path_constraints)
            gas += result.gas

            if opcode.name == 'JUMP':
                # NOTE: add tag to the path list
                state.path.add_node(node)

                node_state = deepcopy(state)
                node_state.set_gas(gas)
                node.set_state(node_state)

                new_edge = Edge(node.tag, result.jump_tag)
                if new_edge in cfg.edges:
                    edge = cfg.get_edge(node.tag, result.jump_tag)
                    edge.change_color()
                else:
                    cfg.add_edge(new_edge)

                return self.symbolic_execution(result.jump_tag)
            elif opcode.name == 'JUMPI':
                # NOTE: Loop detection
                if LOOP_DETECTION:
                    # TODO: implement loop detection
                    pass
                else:
                    # NOTE: add tag to the path list
                    state.path.add_node(node)

                node_state = deepcopy(state)
                node_state.set_gas(gas)
                node.set_state(node_state)

                # NOTE: Jump to two path
                if is_instance(result.jump_condition, int) and result.jump_condition == 1:
                    return self.symbolic_execution(result.jump_tag)
                elif is_instance(result.jump_condition, int) and result.jump_condition == 0:
                    return self.symbolic_execution(node.tag + 1)
                else:
                    self.path_constraints.add_constraints(result.jump_condition)
                    self.symbolic_execution(result.jump_tag)
                    self.symbolic_execution(node.tag + 1)
                    return