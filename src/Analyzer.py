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

    def start(self):
        for node in self.cfg.nodes:
            if node.color == 'yellow':
                s = State()
                s.memory = {64:128}
                logging.debug('Start From Tag %s' % node.tag)
                self.symbolic_execution(node.tag, Path(), s)

    def symbolic_execution(self, tag: int, path: Path, state: State, loop_path: [int] = None, loop_tag: int = None) -> None:
        from src.Result import Result
        logging.debug('TAG: %s (%s)' % (tag, loop_tag))
        if loop_path:
            print('[PATH]:')
            print(path)
            print(loop_path, '\n')

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
            if result == 'ERROR': 
                return
            # if tag in [2041]:
            #     logging.debug('%s: %s' % (opcode.pc, opcode.name))
            #     logging.debug('Stack: %s\n' % self.to_string(state.stack))
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
                self.__add_edge(Edge(node.tag, result.jump_tag, 'red'))

                if loop_path:
                    return self.symbolic_execution(loop_path.pop(0), path, state, loop_path, loop_tag)

                return self.symbolic_execution(result.jump_tag, path, state, loop_tag)
            elif opcode.name == 'JUMPI':
                tmp_cond = simplify(result.jump_condition) if is_expr(result.jump_condition) else result.jump_condition
                result.jump_condition = int(tmp_cond.as_long()) if isinstance(tmp_cond, BitVecNumRef) else result.jump_condition

                node.set_path_constraint(result.jump_condition)
                # NOTE: Loop detection
                detect_loop = False
                if LOOP_DETECTION:
                    if path.count_specific_node_num(node.tag) > 0 and is_expr(result.jump_condition):
                        jump_condition, jump_condition_n1 = path.handle_loop(node, opcode.pc, self.variables)
                        
                        if jump_condition is not None:
                            detect_loop = True
                            result.jump_condition = jump_condition if str(jump_condition) != 'same' else result.jump_condition
                        elif path.count_specific_node_num(node.tag) >= MAX_LOOP_ITERATIONS - 1:
                             # LOG ERROR
                            err_result = Result()
                            err_message = 'Loop Error:[%s] %s' % (tag, result.jump_condition)
                            err_result.log_error(settings.ADDRESS, err_message)
                            raise ValueError(err_message)
                else:
                    path_cond = simplify(node.path_constraint) if is_expr(node.path_constraint) else node.path_constraint

                    if loop_path is not None:
                        print('[JUMPI LOOP]:', tag, loop_tag, path.count_specific_node_num(node.tag), loop_path)
                    if path.count_specific_node_num(node.tag) > 0 and is_expr(path_cond):
                        if loop_path is None:
                            loop_tag, loop_path = path.find_loop_path(node)
                            print('[LOOP]:', loop_tag, loop_path)
                            path.add_node(deepcopy(node))
                            next_tag = loop_path.pop(0)
                            if next_tag == opcode.get_next_pc():
                                path.add_path_constraints([result.jump_condition==0])
                            else:
                                path.add_path_constraints([result.jump_condition==1])
                            return self.symbolic_execution(next_tag, deepcopy(path), deepcopy(state), loop_path, loop_tag)
                        elif loop_tag != tag:
                            path.add_node(deepcopy(node))
                            next_tag = loop_path.pop(0)
                            if next_tag == opcode.get_next_pc():
                                path.add_path_constraints([result.jump_condition==0])
                            else:
                                path.add_path_constraints([result.jump_condition==1])
                            self.symbolic_execution(next_tag, deepcopy(path), deepcopy(state), loop_path, loop_tag)

                            new_loop_tag, new_loop_path = path.find_loop_path(node)
                            print('[LOOP]:', new_loop_tag, new_loop_path)
                            new_next_tag = new_loop_path.pop(0)
                            return self.symbolic_execution(new_next_tag, deepcopy(path), deepcopy(state), new_loop_path, new_loop_tag)

                    if loop_tag == tag and path.count_specific_node_num(node.tag) >= MAX_LOOP_ITERATIONS and is_expr(path_cond):
                        print('MAX LOOP:', tag)
                        for node in self.cfg.nodes:
                            if node.tag == tag:
                                node.loop_condition.append(path.find_loop_condition(node))
                        return

                # NOTE: if edge is not in edges -> add edge into edges
                self.__add_edge(Edge(node.tag, result.jump_tag, 'red'))
                self.__add_edge(Edge(node.tag, opcode.get_next_pc(), 'red'))
                edge_true = self.cfg.get_edge(node.tag, result.jump_tag)
                edge_false = self.cfg.get_edge(node.tag, opcode.get_next_pc())

                if detect_loop:
                    edge_true.set_path_constraint(self.to_string(simplify(result.jump_condition==1)))
                    edge_false.set_path_constraint(self.to_string(simplify(result.jump_condition==0)))
                    
                    if path.contain_node(result.jump_tag):
                        jump_condition_n1 = 0 if jump_condition_n1 is None else jump_condition_n1
                        path.add_path_constraints([result.jump_condition==0, jump_condition_n1==0])
                        return self.symbolic_execution(opcode.get_next_pc(), deepcopy(path), deepcopy(state))
                    elif path.contain_node(opcode.get_next_pc()):
                        jump_condition_n1 = 1 if jump_condition_n1 is None else jump_condition_n1
                        path.add_path_constraints([result.jump_condition==1, jump_condition_n1==1])
                        return self.symbolic_execution(result.jump_tag, deepcopy(path), deepcopy(state))
                    else:
                        # LOG ERROR
                        err_result = Result()
                        err_message = 'Loop Error:[%s] Both JUMPDEST tags have been executed' % tag
                        err_result.log_error(settings.ADDRESS, err_message)
                        raise ValueError(err_message)
                elif loop_path:
                    path.add_node(deepcopy(node))
                    next_tag = loop_path.pop(0)
                    if next_tag == opcode.get_next_pc():
                        path.add_path_constraints([result.jump_condition==0])
                    else:
                        path.add_path_constraints([result.jump_condition==1])
                    return self.symbolic_execution(next_tag, deepcopy(path), deepcopy(state), loop_path, loop_tag)
                else:
                    # NOTE: set gas to node
                    node.set_gas(gas)
                    node.set_state(deepcopy(state))

                    # NOTE: add tag to the path list
                    path.add_node(deepcopy(node))

                    # NOTE: Jump to two path
                    # if tag == 0:
                    # edge_false.set_path_constraint(self.to_string(simplify(result.jump_condition==0)))
                    # return self.symbolic_execution(opcode.get_next_pc(), deepcopy(path), deepcopy(state))

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
                # NOTE: set gas to node
                node.set_gas(gas)
                node.set_state(deepcopy(state))

                # NOTE: add tag to the path list
                path.add_node(deepcopy(node))

                # NOTE: simplify gas formula
                path.gas = simplify(path.gas) if is_expr(path.gas) else int(path.gas)
                path.gas = int(path.gas.as_long()) if isinstance(path.gas, BitVecNumRef) else path.gas
                path.gas = int(path.gas) if isinstance(path.gas, float) else path.gas

                # NOTE: solve gas satisfiability & set gas type
                if path.solve():
                    if isinstance(path.gas, int):
                        path.set_gas_type('constant')
                    elif 'loop' in str(path.gas) and path.solve_unbound():
                        settings.DETECT_LOOP = True
                        path.set_gas_type('unbound')
                        logging.debug('Detect loop')
                    else:
                        path.set_gas_type('bound')
                    self.paths.append(path)
                    self.count_path += 1
                    logging.debug('Finish one path...[%s]' % self.count_path)
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
        self.__add_edge(Edge(node.tag, opcode.get_next_pc(), 'red'))

        return self.symbolic_execution(opcode.get_next_pc(), path, state, loop_path)

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
        self.cfg.render(settings.CFG_PATH)
    
    def to_string(self, input: Any) -> str:
        return str(input).replace('\n', '').replace(' ', '').replace(",'", ",\n'")

    def set_paths_id(self) -> None:
        count_id = 1
        for path in self.paths:
            path.set_id(count_id)
            count_id += 1