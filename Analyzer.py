from global_constants import logging, LOOP_DETECTION, MAX_LOOP_ITERATIONS
from copy import deepcopy
from Cfg import Cfg
from Opcode import Opcode
from Node import Node
from Edge import Edge
from State import State
from PathConstraints import PathConstraints
from Path import Path
from Variable import Variables

class Analyzer:

    def __init__(self, cfg: Cfg):
        self.cfg = cfg
        self.state = State()
        self.path = Path()
        self.variables = Variables()

    def symbolic_execution(self, tag: int, path: Path):
        self.path = path
        node = self.cfg.get_node(tag)
        gas = 0

        for opcode in node.opcodes:
            # NOTE: state simulation
            result = state.simulate(opcode, self.variables)
            self.path.add_path_constraints(result.path_constraints)
            gas += result.gas

            if opcode.name == 'JUMP':
                # NOTE: set gas to node
                node.set_gas(gas)

                # NOTE: add tag to the path list
                self.path.add_node(deepcopy(node))

                # NOTE: if edge is not in edges -> add edge into edges
                self.__add_edge(Edge(node.tag, result.jump_tag))

                return self.symbolic_execution(result.jump_tag, self.path)
            elif opcode.name == 'JUMPI':
                # NOTE: Loop detection
                if LOOP_DETECTION:
                    # TODO: implement loop detection
                    pass
                else:
                    if self.path.count_specific_node_num(node.tag) >= MAX_LOOP_ITERATIONS:
                        return

                # NOTE: set gas to node
                node.set_gas(gas)

                # NOTE: add tag to the path list
                self.path.add_node(deepcopy(node))

                # NOTE: if edge is not in edges -> add edge into edges
                self.__add_edge(Edge(node.tag, result.jump_tag))
                self.__add_edge(Edge(node.tag, node.tag + 1))

                # NOTE: Jump to two path
                if is_instance(result.jump_condition, int) and result.jump_condition == 1:
                    return self.symbolic_execution(result.jump_tag, deepcopy(self.path))
                elif is_instance(result.jump_condition, int) and result.jump_condition == 0:
                    return self.symbolic_execution(node.tag + 1, deepcopy(self.path))
                else:
                    self.path_constraints.add_constraints(result.jump_condition)
                    self.symbolic_execution(result.jump_tag, deepcopy(self.path))
                    self.symbolic_execution(node.tag + 1, deepcopy(self.path))
                    return
            elif opcode.name in ['STOP', 'RETURN', 'REVERT', 'INVALID', 'SELFDESTRUCT']:
                # NOTE: set gas to node
                node.set_gas(gas)

                # NOTE: add tag to the path list
                self.path.add_node(deepcopy(node))

                # TODO: implement analyzed path
        
        """
        NOTE:
            the end of the node is not in block ins -> jump to next node
        """
        # NOTE: set gas to node
        node.set_gas(gas)

        # NOTE: add tag to the path list
        self.path.add_node(deepcopy(node))

        # NOTE: if edge is not in edges -> add edge into edges
        self.__add_edge(Edge(node.tag, node.tag + 1))

        return self.symbolic_execution(node.tag + 1, self.path)

    def __add_edge(self, edge: Edge):
        # NOTE: if edge is not in edges -> add edge into edges
        if edge in self.cfg.edges:
            edge = self.cfg.get_edge(node.tag, result.jump_tag)
            edge.change_color()
        else:
            self.cfg.add_edge(new_edge)
