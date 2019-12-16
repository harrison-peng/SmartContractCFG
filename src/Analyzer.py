import src.settings as settings
from src.settings import logging, LOOP_DETECTION, MAX_LOOP_ITERATIONS, ENABLE_MAX_NODE_VISITED_TIMES, MAX_NODE_VISITED_TIMES
from z3 import *
from typing import Any
from copy import deepcopy
from src.Cfg import Cfg
from src.Opcode import Opcode
from src.Node import Node
from src.Edge import Edge
from src.State import State
from src.Path import Path
from src.Variable import Variables

class Analyzer:

    def __init__(self, cfg: Cfg):
        self.cfg = cfg
        self.paths = list()
        self.variables = Variables()
        self.count_path = 0

    def symbolic_execution(self, tag: int, path: Path, state: State) -> None:
        logging.debug('TAG: %s' % tag)

        if settings.DETECT_LOOP:
            return 

        node = self.cfg.get_node(tag)
        if not node:
            return
        node.visit()
        gas = 0

        if node.count % 10 == 0:
            logging.debug('%s visit %s times' % (tag, node.count))
        if ENABLE_MAX_NODE_VISITED_TIMES and node.count > MAX_NODE_VISITED_TIMES:
            return

        for opcode in node.opcodes:
            # NOTE: state simulation
            result = state.simulate(opcode, self.variables)
            # if tag in [102]:
            #     logging.debug('%s: %s' % (opcode.pc, opcode.name))
            #     logging.debug('Stack: %s\n\n' % self.to_string(state.stack))
            #     logging.debug('MEM: %s' % self.to_string(state.memory))
            #     logging.debug('STO: %s\n' % self.to_string(state.storage))
            path.add_path_constraints(result.path_constraints)
            gas += result.gas
            gas = simplify(gas) if is_expr(gas) else gas
            path.add_gas(result.gas)
            path.add_memory_gas(result.memory_gas)
            

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
                # NOTE: Loop detection
                detect_loop = False
                if LOOP_DETECTION:
                    if path.count_specific_node_num(node.tag) > 0 and is_expr(result.jump_condition):
                        jump_condition = path.handle_loop(node, opcode.pc, self.variables)
                        if jump_condition is not False or path.count_specific_node_num(node.tag) >= MAX_LOOP_ITERATIONS - 1:
                            detect_loop = True
                            if jump_condition is not False:
                                result.jump_condition = jump_condition
                else:
                    if path.count_specific_node_num(node.tag) >= MAX_LOOP_ITERATIONS:
                        return

                # NOTE: if edge is not in edges -> add edge into edges
                self.__add_edge(Edge(node.tag, result.jump_tag))
                self.__add_edge(Edge(node.tag, opcode.get_next_pc()))
                edge_true = self.cfg.get_edge(node.tag, result.jump_tag)
                edge_false = self.cfg.get_edge(node.tag, opcode.get_next_pc())

                if detect_loop:
                    edge_true.set_path_constraint(self.to_string(simplify(result.jump_condition==1)))
                    edge_false.set_path_constraint(self.to_string(simplify(result.jump_condition==0)))
                    
                    if path.contain_node(result.jump_tag) and path.contain_node(opcode.get_next_pc()):
                        return
                    else:
                        if path.contain_node(result.jump_tag):
                            path.add_path_constraints([result.jump_condition==0])
                            return self.symbolic_execution(opcode.get_next_pc(), deepcopy(path), deepcopy(state))
                        else:
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
                        edge_true.set_path_constraint('True')
                        edge_false.set_path_constraint('False')
                        return self.symbolic_execution(result.jump_tag, deepcopy(path), deepcopy(state))
                    elif isinstance(result.jump_condition, int) and result.jump_condition == 0:
                        edge_true.set_path_constraint('False')
                        edge_false.set_path_constraint('True')
                        return self.symbolic_execution(opcode.get_next_pc(), deepcopy(path), deepcopy(state))
                    elif isinstance(result.jump_condition, int):
                        return
                    else:
                        edge_true.set_path_constraint(self.to_string(simplify(result.jump_condition==1)))
                        edge_false.set_path_constraint(self.to_string(simplify(result.jump_condition==0)))
                        true_path, false_path = deepcopy(path), deepcopy(path)
                        true_state, false_state = deepcopy(state), deepcopy(state)
                        true_path.add_path_constraints([result.jump_condition==1])
                        false_path.add_path_constraints([result.jump_condition==0])
                        self.symbolic_execution(result.jump_tag, true_path, true_state)
                        self.symbolic_execution(opcode.get_next_pc(), false_path, false_state)
                        return
            elif opcode.name in ['STOP', 'RETURN', 'REVERT', 'INVALID', 'SELFDESTRUCT']:
                self.count_path += 1
                logging.debug('Finish one path...[%s]' % self.count_path)
                # NOTE: set gas to node
                node.set_gas(gas)
                node.set_state(deepcopy(state))

                # NOTE: add tag to the path list
                path.add_node(deepcopy(node))
                self.paths.append(path)
                if 'loop' in str(path.gas) and path.solve():
                    settings.DETECT_LOOP = True
                    logging.debug('Detect loop')
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

    def symbolic_execution_from_other_head(self) -> None:
        from_list = [edge.from_ for edge in self.cfg.edges]
        to_list = [edge.to_ for edge in self.cfg.edges]
        node_list = [node for node in self.cfg.nodes if node.tag in from_list and node.tag not in to_list]
        for node in node_list:
            state = State()
            state.init_with_var(self.variables)
            self.symbolic_execution(node.tag, Path(), state)

    def __add_edge(self, edge: Edge) -> None:
        # NOTE: if edge is not in edges -> add edge into edges
        for e in self.cfg.edges:
            if e == edge:
                e.change_color()
                return
        self.cfg.add_edge(edge)
    
    def to_string(self, input: Any) -> str:
        return str(input).replace('\n', '').replace(' ', '').replace(",'", ",\n'")

    def set_paths_id(self) -> None:
        count_id = 1
        for path in self.paths:
            path.set_id(count_id)
            count_id += 1