import src.settings as settings
from typing import Any
from src.settings import logging, UNSIGNED_BOUND_NUMBER, TIMEOUT, GAS_LIMIT
from z3 import *
from src.Node import Node
from src.State import State
from src.Variable import Variable, Variables

class Path:

    def __init__(self):
        self.id = None
        self.path = list()
        self.path_constraint = list()
        self.gas = 0
        self.memory_gas = 0
        self.solver = Solver()
        self.gas_type = None
        self.model = None
        self.model_gas = None

    def __str__(self) -> str:
        return '[%s]: %s' % (self.id, self.path)

    def __repr__(self) -> str:
        return '<%s object>[%s]: %s' % (self.__class__.__name__, self.id, self.path)

    def set_id(self, id: int) -> None:
        self.id = id

    def set_gas_type(self, gas_type: str) -> None:
        self.gas_type = gas_type

    def add_node(self, node: Node) -> None:
        self.path.append(node)

    def add_path_constraints(self, constraints: list) -> None:
        self.path_constraint += constraints

    def count_specific_node_num(self, tag: int) -> int:
        return len([node for node in self.path if node.tag == tag])

    def add_gas(self, gas: int) -> None:
        self.gas += gas
        self.gas = simplify(self.gas) if is_expr(self.gas) else int(self.gas)

    def add_memory_gas(self, gas: int) -> None:
        self.memory_gas += gas
        self.memory_gas = simplify(self.memory_gas) if is_expr(self.memory_gas) else int(self.memory_gas)

    def contain_node(self, tag: int) -> bool:
        for node in self.path:
            if node.tag == tag:
                return True
        return False

    def node_last_index(self, tag: int) -> int:
        return [index for index, node in enumerate(self.path) if node.tag == tag][-1]

    def handle_loop(self, incoming_node: Node, pc: int, variables: list) -> ArithRef:
        nodes = list()
        for node in self.path:
            if node.tag == incoming_node.tag:
                nodes.append(node)
        nodes.append(incoming_node)

        loop_formula, loop_formula_n = self.__extrapolation(nodes[-2:], pc, variables)
        if loop_formula is None and len(nodes) > 2:
            loop_formula = self.__switch_constraint(nodes[-3:])
        
        if loop_formula is not None and str(loop_formula) != 'same':
            loop_var = variables.get_variable(Variable('loop_%s' % pc, 'Loop iteration of pc: %s' % pc, BitVec('loop_%s' % pc, 256)))
            self.__handle_loop_gas(incoming_node.tag, loop_var)
            if len(nodes) > 2:
                self.__fix_loop_path(incoming_node.tag, len(nodes))
        return loop_formula, loop_formula_n

    def __extrapolation(self, nodes: list, pc: int, variables: list) -> (ArithRef, ArithRef):
        from src.Result import Result
        decl, constraint, formulae = list(), list(), list()
        
        for node in nodes:
            constraint.append(self.to_string(node.path_constraint))
        if len(set(constraint)) == 1:
            return 'same', None

        for i, node in enumerate(nodes):
            formula, if_pair = self.__unpack_z3_if(node.path_constraint)
            if formula is None:
                return None, None
            decl.append(formula.decl())
            formulae.append(formula.arg(0) - formula.arg(1))
        
        diff = simplify(formulae[1] - formulae[0])
        diff = int(diff.as_long()) if isinstance(diff, BitVecNumRef) else diff
        # logging.debug('Loop constraint diff: %s' % diff)

        if len(set(decl)) == 1:
            if isinstance(diff, int):
                if diff != 0:
                    loop_var = variables.get_variable(Variable('loop_%s' % pc, 'Loop iteration of pc: %s' % pc, BitVec('loop_%s' % pc, 256)))
                    self.path_constraint.append(ULT(loop_var, UNSIGNED_BOUND_NUMBER))
                    loop_formula = If(decl[0](formulae[0] + diff*loop_var, 0), if_pair[0], if_pair[1])
                    loop_formula_n = If(decl[0](formulae[0] + diff*(loop_var + 1), 0), if_pair[1], if_pair[0])
                else:
                    loop_formula = 'same'
                    loop_formula_n = None
            else:
                loop_formula = None
                loop_formula_n = None
        else:
            result = Result()
            result.log_error(settings.ADDRESS, 'Operators are not same')
            raise ValueError('Operators are not same: %s' % decl)
            
        if loop_formula is not None:
            for i, node in enumerate(nodes):
                self.__remove_constraint_from_path(node.path_constraint)
        else:
            logging.debug('Cannot solve loop formula: %s' % formulae)

        return loop_formula, loop_formula_n

    def __switch_constraint(self, nodes: list) -> ArithRef:
        formula_1, if_pair = self.__unpack_z3_if(nodes[0].path_constraint)
        formula_2, if_pair = self.__unpack_z3_if(nodes[1].path_constraint)
        formula_3, if_pair = self.__unpack_z3_if(nodes[2].path_constraint)
        if self.to_string(formula_1) == self.to_string(formula_3):
            return If(Or(formula_1, formula_2), if_pair[0], if_pair[1])
        else:
            return None

    def __unpack_z3_if(self, formula: ArithRef) -> ArithRef:
        from src.Result import Result
        try:
            formula = int(formula.as_long) if isinstance(formula, BitVecNumRef) else formula
            if is_expr(formula) and str(formula.decl()) == 'If':
                return self.__unpack_z3_if(formula.arg(0)), (formula.arg(1), formula.arg(2))
            elif isinstance(formula, z3.z3.BitVecRef):
                return None, None
            else:
                return formula
        except Exception as e:
            err_result = Result()
            err_result.log_error(settings.ADDRESS, 'Cannot unpack z3 if')
            raise ValueError('Cannot unpack z3 if [%s]: %s' % (formula, e))

    def to_string(self, input: Any) -> str:
        return str(input).replace('\n', '').replace(' ', '').replace(",'", ",\n'")

    def __remove_constraint_from_path(self, node_constraint: ArithRef) -> None:
        for constraint in self.path_constraint[::-1]:
            constraint_str = self.to_string(constraint)
            node_constraint_true_str = self.to_string(node_constraint == 1)
            node_constraint_false_str = self.to_string(node_constraint == 0)
            if constraint_str == node_constraint_true_str or constraint_str == node_constraint_false_str:
                self.path_constraint.remove(constraint)
                return

    def __handle_loop_gas(self, tag: int, loop_var: BitVecRef) -> int:
        from src.Result import Result
        gas = 0
        index = [index for index, node in enumerate(self.path) if node.tag == tag]
        path = self.path[index[0]:index[1]] if len(index) > 1 else self.path[index[0]:]
        for node in path:
            gas += node.gas
        gas = gas * BV2Int(loop_var)
        gas = simplify(gas) if is_expr(gas) else int(gas)
        self.add_gas(gas)

    def __fix_loop_path(self, tag: int, loop_num: int) -> None:
        count_loop_node = 0
        for index, node in enumerate(self.path):
            if node.tag == tag:
                count_loop_node += 1
                if count_loop_node == loop_num - 1:
                    stop_index = index + 1
                    break
        for node in self.path[stop_index:]:
            self.gas -= node.gas
        self.gas = simplify(self.gas) if is_expr(self.gas) else int(self.gas)
        self.path = self.path[:index + 1]

    def solve(self) -> bool:
        for contraint in self.path_constraint:
            self.solver.add(contraint)
        self.solver.set(timeout=TIMEOUT)
        if self.solver.check() == sat:
            self.model = self.solver.model()
            return True
        return False

    def solve_max_gas(self, gas: int) -> bool:
        self.solver.push()
        self.solver.add(self.gas > gas)
        is_sat = False
        self.solver.set(timeout=TIMEOUT)
        while self.solver.check() == sat:
            logging.debug('SAT: %s' % gas)
            is_sat = True
            gas += 10000
            self.solver.pop()
            self.solver.push()
            self.solver.add(self.gas > gas)
            self.solver.set(timeout=TIMEOUT)
        else:
            logging.debug('UNSAT: %s' % gas)
        self.solver.pop()
        self.solver.push()
        self.solver.add(self.gas > gas - 10000)
        self.solver.set(timeout=TIMEOUT)
        if self.solver.check() == sat:
            self.model = self.solver.model()
            return True
        else:
            if is_sat:
                result = Result()
                result.log_error(settings.ADDRESS, 'Solver Error')
                raise ValueError('Solver Error')
            else:
                return False

    def solve_unbound(self) -> bool:
        self.solver.add(self.gas > GAS_LIMIT)
        self.solver.set(timeout=TIMEOUT)
        if self.solver.check() == sat:
            self.model = self.solver.model()
            return True
        return False

    def assign_model(self, variables: Variables) -> int:
        logging.debug('Assign model into cfg...')
        gas = 0
        state = State()
        for node in self.path:
            for opcode in node.opcodes:
                gas += state.simulate_with_model(opcode, self.model, variables)
        self.model_gas = gas