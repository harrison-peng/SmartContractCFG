from settings import logging, LOOP_DETECTION, MAX_LOOP_ITERATIONS
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
        self.paths = list()

    def symbolic_execution(self, tag: int, path: Path, state: State):
        logging.debug('TAG: %s' % tag)
        node = self.cfg.get_node(tag)
        node.visite()
        gas = 0

        for opcode in node.opcodes:
            # NOTE: state simulation
            result = state.simulate(opcode)
            # if tag in [517, 1513, 1530, 2940, 2948, 1415, 1563, 3055]:
            #     logging.debug('%s: %s' % (opcode.pc, opcode.name))
            #     logging.debug('Stack: %s\n\n' % self.to_string(state.stack))
            #     logging.debug('MEM: %s' % self.to_string(state.memory))
            #     logging.debug('STO: %s\n' % self.to_string(state.storage))
            path.add_path_constraints(result.path_constraints)
            gas += result.gas
            gas = simplify(gas) if is_expr(gas) else gas
            path.add_gas(result.gas)
            

            if opcode.name == 'JUMP':
                # NOTE: set gas to node
                node.set_gas(gas)
                node.set_state(deepcopy(state))

                # NOTE: add tag to the path list
                path.add_node(deepcopy(node))

                # NOTE: if edge is not in edges -> add edge into edges
                self.__add_edge(Edge(node.tag, result.jump_tag))

                return self.symbolic_execution(result.jump_tag, path, state)
            elif opcode.name == 'JUMPI':
                node.set_path_constraint(result.jump_condition)
                # logging.debug('JUMPI condition: %s' % result.jump_condition)
                # NOTE: Loop detection
                detect_loop = False
                if LOOP_DETECTION:
                    if path.count_specific_node_num(node.tag) >= MAX_LOOP_ITERATIONS and is_expr(result.jump_condition):
                        detect_loop = True
                        result.jump_condition = path.handle_loop(node, opcode.pc)

                else:
                    # logging.debug('%s: %s\n\n' % (tag, path))
                    if path.count_specific_node_num(node.tag) >= MAX_LOOP_ITERATIONS:
                        return

                # NOTE: if edge is not in edges -> add edge into edges
                self.__add_edge(Edge(node.tag, result.jump_tag))
                self.__add_edge(Edge(node.tag, opcode.get_next_pc()))
                edge_true = self.cfg.get_edge(node.tag, result.jump_tag)
                edge_false = self.cfg.get_edge(node.tag, opcode.get_next_pc())

                if detect_loop:
                    logging.debug('DETECT LOOP: %s' % tag)
                    # logging.debug('%s' % path)
                    edge_true.set_path_constraint(str(simplify(result.jump_condition==1)).replace('\n', '').replace('\t', '').replace(' ', ''))
                    edge_false.set_path_constraint(str(simplify(result.jump_condition==0)).replace('\n', '').replace('\t', '').replace(' ', ''))
                    
                    if path.contain_node(result.jump_tag) and path.contain_node(opcode.get_next_pc()):
                        logging.debug('LOOP STOP')
                        return
                    else:
                        if path.contain_node(result.jump_tag):
                            logging.debug('LOOP GO FALSE: [%s, %s]' % (result.jump_tag, opcode.get_next_pc()))
                            # logging.debug('%s' % path)
                            path.add_path_constraints([result.jump_condition==0])
                            return self.symbolic_execution(opcode.get_next_pc(), deepcopy(path), deepcopy(state))
                        else:
                            logging.debug('LOOP GO TRUE: [%s, %s]' % (result.jump_tag, opcode.get_next_pc()))
                            # logging.debug('%s' % path)
                            path.add_path_constraints([result.jump_condition==1])
                            return self.symbolic_execution(result.jump_tag, deepcopy(path), deepcopy(state))
                else:
                    # NOTE: set gas to node
                    node.set_gas(gas)
                    node.set_state(deepcopy(state))

                    # NOTE: add tag to the path list
                    path.add_node(deepcopy(node))

                    # NOTE: Jump to two path
                    if isinstance(result.jump_condition, int) and result.jump_condition == 1:
                        # logging.debug('Tag: %s Go True' % tag)
                        edge_true.set_path_constraint('True')
                        edge_false.set_path_constraint('False')
                        return self.symbolic_execution(result.jump_tag, deepcopy(path), deepcopy(state))
                    elif isinstance(result.jump_condition, int) and result.jump_condition == 0:
                        # logging.debug('Tag: %s Go False' % tag)
                        edge_true.set_path_constraint('False')
                        edge_false.set_path_constraint('True')
                        return self.symbolic_execution(opcode.get_next_pc(), deepcopy(path), deepcopy(state))
                    else:
                        # logging.debug('Tag: %s Go Both' % tag)
                        edge_true.set_path_constraint(str(simplify(result.jump_condition==1)).replace('\n', '').replace('\t', '').replace(' ', ''))
                        edge_false.set_path_constraint(str(simplify(result.jump_condition==0)).replace('\n', '').replace('\t', '').replace(' ', ''))
                        true_path, false_path = deepcopy(path), deepcopy(path)
                        true_state, false_state = deepcopy(state), deepcopy(state)
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
                path.add_node(deepcopy(node))
                self.paths.append(path)
                # logging.debug(path)
                return
        
        """
        NOTE:
            the end of the node is not in block ins -> jump to next node
        """
        # NOTE: set gas to node
        node.set_gas(gas)

        # NOTE: add tag to the path list
        path.add_node(deepcopy(node))

        # NOTE: if edge is not in edges -> add edge into edges
        self.__add_edge(Edge(node.tag, opcode.get_next_pc()))

        return self.symbolic_execution(opcode.get_next_pc(), path, state)

    def symbolic_execution_from_node(self):
        from_list = [edge.from_ for edge in self.cfg.edges]
        to_list = [edge.to_ for edge in self.cfg.edges]
        node_list = [node for node in self.cfg.nodes if node.tag in from_list and node.tag not in to_list]
        # logging.debug('NODE: %s' % len(node_list))
        for node in node_list:
            state = State()
            state.init_with_var()
            self.symbolic_execution(node.tag, Path(), state)

    def __add_edge(self, edge: Edge):
        # NOTE: if edge is not in edges -> add edge into edges
        for e in self.cfg.edges:
            if e == edge:
                e.change_color()
                return
        self.cfg.add_edge(edge)
    
    def to_string(self, input: Any) -> str:
        return str(input).replace('\n', '').replace(' ', '').replace(",'", ",\n'")
