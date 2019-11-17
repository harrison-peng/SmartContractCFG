from global_constants import logging, LOOP_DETECTION, MAX_LOOP_ITERATIONS, PATHS
from copy import deepcopy
from Cfg import Cfg
from Opcode import Opcode
from Node import Node
from Edge import Edge
from State import State
from PathConstraint import PathConstraint
from Path import Path

class Analyzer:

    def __init__(self, cfg: Cfg):
        self.cfg = cfg
        self.state = State()
        self.path = Path()

    def symbolic_execution(self, tag: int, path: Path, state: State):
        logging.debug('TAG: %s' % tag)
        self.state = state
        self.path = path
        node = self.cfg.get_node(tag)
        gas = 0

        for opcode in node.opcodes:
            # NOTE: state simulation
            result = self.state.simulate(opcode)
            # if tag in [0, 13, 65, 76, 87, 98, 109, 120, 131, 142, 948, 960, 2961, 3053, 3107, 3260, 969]:
            #     logging.debug('%s: %s %s\n' % (opcode.pc, opcode.name, self.state.stack))
            self.path.add_path_constraints(result.path_constraints)
            gas += result.gas

            if opcode.name == 'JUMP':
                # NOTE: set gas to node
                node.set_gas(gas)

                # NOTE: add tag to the path list
                self.path.add_node(deepcopy(node))

                # NOTE: if edge is not in edges -> add edge into edges
                self.__add_edge(Edge(node.tag, result.jump_tag))

                return self.symbolic_execution(result.jump_tag, self.path, self.state)
            elif opcode.name == 'JUMPI':
                # logging.debug('JUMPI condition: %s' % result.jump_condition)
                # NOTE: Loop detection
                if LOOP_DETECTION:
                    # TODO: implement loop detection
                    pass
                else:
                    # logging.debug('%s: %s\n\n' % (tag, self.path))
                    if self.path.count_specific_node_num(node.tag) >= MAX_LOOP_ITERATIONS:
                        return

                # NOTE: set gas to node
                node.set_gas(gas)

                # NOTE: add tag to the path list
                self.path.add_node(deepcopy(node))

                # NOTE: if edge is not in edges -> add edge into edges
                self.__add_edge(Edge(node.tag, result.jump_tag))
                self.__add_edge(Edge(node.tag, opcode.get_next_pc()))

                # NOTE: Jump to two path
                if isinstance(result.jump_condition, int) and result.jump_condition == 1:
                    # logging.debug('Tag: %s Go True' % tag)
                    return self.symbolic_execution(result.jump_tag, deepcopy(self.path), deepcopy(self.state))
                elif isinstance(result.jump_condition, int) and result.jump_condition == 0:
                    # logging.debug('Tag: %s Go False' % tag)
                    return self.symbolic_execution(opcode.get_next_pc(), deepcopy(self.path), deepcopy(self.state))
                else:
                    # logging.debug('Tag: %s Go Both' % tag)
                    true_path, false_path = deepcopy(self.path), deepcopy(self.path)
                    true_state, false_state = deepcopy(self.state), deepcopy(self.state)
                    self.path.add_path_constraints([result.jump_condition])
                    self.symbolic_execution(result.jump_tag, true_path, true_state)
                    self.symbolic_execution(opcode.get_next_pc(), false_path, false_state)
                    return
            elif opcode.name in ['STOP', 'RETURN', 'REVERT', 'INVALID', 'SELFDESTRUCT']:
                # NOTE: set gas to node
                node.set_gas(gas)

                # NOTE: add tag to the path list
                self.path.add_node(deepcopy(node))

                # TODO: implement analyzed path
                PATHS.append(self.path)
                # logging.debug(self.path)
                return
        
        """
        NOTE:
            the end of the node is not in block ins -> jump to next node
        """
        # NOTE: set gas to node
        node.set_gas(gas)

        # NOTE: add tag to the path list
        self.path.add_node(deepcopy(node))

        # NOTE: if edge is not in edges -> add edge into edges
        self.__add_edge(Edge(node.tag, opcode.get_next_pc()))

        return self.symbolic_execution(opcode.get_next_pc(), self.path, self.state)

    def __add_edge(self, edge: Edge):
        # NOTE: if edge is not in edges -> add edge into edges
        if edge in self.cfg.edges:
            edge = self.cfg.get_edge(edge.from_, edge.to_)
            edge.change_color()
        else:
            self.cfg.add_edge(edge)
