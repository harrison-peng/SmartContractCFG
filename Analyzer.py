from settings import logging, LOOP_DETECTION, MAX_LOOP_ITERATIONS, PATHS
from z3 import *
from typing import Any
from copy import deepcopy
from Cfg import Cfg
from Opcode import Opcode
from Node import Node
from Edge import Edge
from State import State
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
            # if tag in [4778, 4843, 4858, 4861,4870]:
            #     logging.debug('%s: %s' % (opcode.pc, opcode.name))
            #     logging.debug('Stack: %s\n\n' % self.to_string(self.state.stack))
                # logging.debug('MEM: %s' % self.to_string(self.state.memory))
                # logging.debug('STO: %s\n' % self.to_string(self.state.storage))
            self.path.add_path_constraints(result.path_constraints)
            gas += result.gas
            gas = simplify(gas) if is_expr(gas) else gas
            self.path.add_gas(result.gas)
            

            if opcode.name == 'JUMP':
                # NOTE: set gas to node
                node.set_gas(gas)
                node.set_state(deepcopy(state))

                # NOTE: add tag to the path list
                self.path.add_node(deepcopy(node))

                # NOTE: if edge is not in edges -> add edge into edges
                self.__add_edge(Edge(node.tag, result.jump_tag))

                return self.symbolic_execution(result.jump_tag, self.path, self.state)
            elif opcode.name == 'JUMPI':
                node.set_path_constraint(result.jump_condition)
                # logging.debug('JUMPI condition: %s' % result.jump_condition)
                # NOTE: Loop detection
                detect_loop = False
                if LOOP_DETECTION:
                    if self.path.count_specific_node_num(node.tag) >= MAX_LOOP_ITERATIONS and is_expr(result.jump_condition):
                        detect_loop = True
                        result.jump_condition = self.path.handle_loop(node, opcode.pc)

                else:
                    # logging.debug('%s: %s\n\n' % (tag, self.path))
                    if self.path.count_specific_node_num(node.tag) >= MAX_LOOP_ITERATIONS:
                        return

                # NOTE: if edge is not in edges -> add edge into edges
                self.__add_edge(Edge(node.tag, result.jump_tag))
                self.__add_edge(Edge(node.tag, opcode.get_next_pc()))
                edge_true = self.cfg.get_edge(node.tag, result.jump_tag)
                edge_false = self.cfg.get_edge(node.tag, opcode.get_next_pc())

                if detect_loop:
                    logging.debug('DETECT LOOP: %s' % tag)
                    # logging.debug('%s' % self.path)
                    edge_true.set_path_constraint(str(simplify(result.jump_condition==1)).replace('\n', '').replace('\t', '').replace(' ', ''))
                    edge_false.set_path_constraint(str(simplify(result.jump_condition==0)).replace('\n', '').replace('\t', '').replace(' ', ''))
                    
                    if self.path.contain_node(result.jump_tag) and self.path.contain_node(opcode.get_next_pc()):
                        logging.debug('LOOP STOP')
                        return
                    else:
                        if self.path.contain_node(result.jump_tag):
                            logging.debug('LOOP GO FALSE: [%s, %s]' % (result.jump_tag, opcode.get_next_pc()))
                            # logging.debug('%s' % self.path)
                            self.path.add_path_constraints([result.jump_condition==0])
                            return self.symbolic_execution(opcode.get_next_pc(), deepcopy(self.path), deepcopy(self.state))
                        else:
                            logging.debug('LOOP GO TRUE: [%s, %s]' % (result.jump_tag, opcode.get_next_pc()))
                            # logging.debug('%s' % self.path)
                            self.path.add_path_constraints([result.jump_condition==1])
                            return self.symbolic_execution(result.jump_tag, deepcopy(self.path), deepcopy(self.state))
                else:
                    # NOTE: set gas to node
                    node.set_gas(gas)
                    node.set_state(deepcopy(state))

                    # NOTE: add tag to the path list
                    self.path.add_node(deepcopy(node))

                    # NOTE: Jump to two path
                    if isinstance(result.jump_condition, int) and result.jump_condition == 1:
                        # logging.debug('Tag: %s Go True' % tag)
                        edge_true.set_path_constraint('True')
                        edge_false.set_path_constraint('False')
                        return self.symbolic_execution(result.jump_tag, deepcopy(self.path), deepcopy(self.state))
                    elif isinstance(result.jump_condition, int) and result.jump_condition == 0:
                        # logging.debug('Tag: %s Go False' % tag)
                        edge_true.set_path_constraint('False')
                        edge_false.set_path_constraint('True')
                        return self.symbolic_execution(opcode.get_next_pc(), deepcopy(self.path), deepcopy(self.state))
                    else:
                        # logging.debug('Tag: %s Go Both' % tag)
                        edge_true.set_path_constraint(str(simplify(result.jump_condition==1)).replace('\n', '').replace('\t', '').replace(' ', ''))
                        edge_false.set_path_constraint(str(simplify(result.jump_condition==0)).replace('\n', '').replace('\t', '').replace(' ', ''))
                        true_path, false_path = deepcopy(self.path), deepcopy(self.path)
                        true_state, false_state = deepcopy(self.state), deepcopy(self.state)
                        true_path.add_path_constraints([result.jump_condition==1])
                        false_path.add_path_constraints([result.jump_condition==0])
                        self.symbolic_execution(result.jump_tag, true_path, true_state)
                        self.symbolic_execution(opcode.get_next_pc(), false_path, false_state)
                        return
            elif opcode.name in ['STOP', 'RETURN', 'REVERT', 'INVALID', 'SELFDESTRUCT']:
                # NOTE: set gas to node
                node.set_gas(gas)
                node.set_state(deepcopy(state))

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
        for e in self.cfg.edges:
            if e == edge:
                e.change_color()
                return
        self.cfg.add_edge(edge)
    
    def to_string(self, input: Any) -> str:
        return str(input).replace('\n', '').replace(' ', '').replace(",'", ",\n'")
