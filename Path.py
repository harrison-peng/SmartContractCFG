from settings import logging, UNSIGNED_BOUND_NUMBER
from z3 import *
from Node import Node
from State import State
from Variable import Variable, Variables

class Path:

    def __init__(self):
        self.path = list()
        self.path_constraint = list()
        self.gas = 0
        self.solver = Solver()
        self.model = None
        self.model_gas = None

    def __str__(self) -> str:
        return '%s' % self.path

    def __repr__(self) -> str:
        return '<%s object> %s' % (self.__class__.__name__, self.path)

    def add_node(self, node: Node):
        self.path.append(node)

    def add_path_constraints(self, constraints: list):
        self.path_constraint += constraints

    def count_specific_node_num(self, tag: int) -> int:
        return len([node for node in self.path if node.tag == tag])

    def add_gas(self, gas):
        self.gas += gas
        self.gas = simplify(self.gas) if is_expr(self.gas) else int(self.gas)

    def contain_node(self, tag: int) -> bool:
        for node in self.path:
            if node.tag == tag:
                return True
        return False

    def node_last_index(self, tag: int) -> int:
        return [index for index, node in enumerate(self.path) if node.tag == tag][-1]

    def handle_loop(self, incoming_node: Node, pc: int, variables: list) -> ArithRef:
        # logging.debug('Handling loop...')
        nodes = list()
        loop_var = variables.get_variable(Variable('loop_%s' % pc, 'Loop iteration of pc: %s' % pc, BitVec('loop_%s' % pc, 256)))
        self.path_constraint.append(ULT(loop_var, UNSIGNED_BOUND_NUMBER))
        for node in self.path:
            if node.tag == incoming_node.tag:
                nodes.append(node)
        nodes.append(incoming_node)

        loop_formula = self.__handle_loop_constraint(nodes, loop_var)
        self.__handle_loop_gas(incoming_node.tag, loop_var)
        self.__fix_loop_path(incoming_node.tag)
        return loop_formula

    def __unpack_z3_if(self, formula):
        formula = int(formula.as_long) if isinstance(formula, BitVecNumRef) else formula
        if is_expr(formula) and str(formula.decl()) == 'If':
            return self.__unpack_z3_if(formula.arg(0)), (formula.arg(1), formula.arg(2))
        else:
            return formula

    def __handle_loop_constraint(self, nodes: list, loop_var: BitVecRef) -> ArithRef:
        decl, arg_1, arg_2 = list(), list(), list()
        for i, node in enumerate(nodes):
            for constraint in self.path_constraint[::-1]:
                constraint_str = str(constraint).replace('\n', '').replace(' ', '')
                node_constraint_true_str = str(node.path_constraint == 1).replace('\n', '').replace(' ', '')
                node_constraint_false_str = str(node.path_constraint == 0).replace('\n', '').replace(' ', '')
                if node_constraint_true_str == node_constraint_true_str or node_constraint_true_str == node_constraint_false_str:
                    self.path_constraint.remove(constraint)
                    break
            formula, if_pair = self.__unpack_z3_if(node.path_constraint)
            decl.append(formula.decl())
            arg_1.append(formula.arg(0))
            arg_2.append(formula.arg(1))
        if len(set(decl)) == 1:
            loop_formula = self.__produce_loop_formula(loop_var, if_pair, arg_1, arg_2, decl[0])
            if loop_formula is None:
                arg_1.pop(0)
                arg_2.pop(0)
                loop_formula = self.__produce_loop_formula(loop_var, if_pair, arg_1, arg_2, decl[0])
                if loop_formula is None:
                    logging.error('%s %s' % (len(set(arg_1)), len(set(arg_2))))
                    for node in nodes:
                        logging.error('PC: %s' % str(node.path_constraint).replace('\n', '').replace(' ', ''))
                        logging.error('MEM: %s' % str(node.state.memory).replace('\n', '').replace(' ', ''))
                        logging.error('STO: %s' % str(node.state.storage).replace('\n', '').replace(' ', ''))
                    raise ValueError('Both side of formula are not fixed')
        else:
            raise ValueError('Operators are not same')

        # for constraint in self.path_constraint
        return loop_formula

    def __produce_loop_formula(self, loop_var: BitVecRef, if_pair: tuple, arg_1: list, arg_2: list, decl: FuncDeclRef) -> ArithRef:
        if len(set(arg_1)) == 1 and len(set(arg_2)) > 1:
            diff = simplify(arg_2[1] - arg_2[0])
            loop_formula = If(decl(arg_1[0], arg_2[0] + diff*loop_var), if_pair[0], if_pair[1])
        elif len(set(arg_1)) > 1 and len(set(arg_2)) == 1:
            diff = simplify(arg_1[1] - arg_1[0])
            loop_formula = If(decl(arg_1[0] + diff*loop_var, arg_2[0]), if_pair[0], if_pair[1])
        else:
            loop_formula = None
        return loop_formula

    def __handle_loop_gas(self, tag: int, loop_var: BitVecRef) -> int:
        gas = 0
        index = [index for index, node in enumerate(self.path) if node.tag == tag]
        if len(index) > 1:
            for node in self.path[index[0]:index[1]]:
                gas += node.gas
        else:
            raise ValueError('Only one node in the loop path')
        gas = gas * BV2Int(loop_var)
        gas = simplify(gas) if is_expr(gas) else int(gas)
        self.add_gas(gas)

    def __fix_loop_path(self, tag: int):
        count_loop_node = 0
        for index, node in enumerate(self.path):
            if node.tag == tag:
                count_loop_node += 1
                if count_loop_node == 2:
                    stop_index = index + 1
                    break
        for node in self.path[stop_index:]:
            self.gas -= node.gas
        self.gas = simplify(self.gas) if is_expr(self.gas) else int(self.gas)
        self.path = self.path[:index + 1]

    def gas_type(self) -> str:
        self.gas = simplify(self.gas) if is_expr(self.gas) else int(self.gas)
        self.gas = int(self.gas.as_long) if isinstance(self.gas, BitVecNumRef) else self.gas
        self.gas = int(self.gas) if isinstance(self.gas, float) else self.gas
        if isinstance(self.gas, int):
            return 'CONSTANT'
        elif 'loop' in str(self.gas):
            return 'UNBOUND'
        else:
            return 'BOUND'

    def solve(self):
        # logging.debug('Solving the constraints...')
        for contraint in self.path_constraint:
            self.solver.add(contraint)
        if self.solver.check() == sat:
            self.model = self.solver.model()
            return True
        return False

    def solve_max_gas(self, gas: int) -> bool:
        # logging.debug('Finding max gas...')
        self.solver.push()
        self.solver.add(self.gas > gas)
        is_sat = False
        while self.solver.check() == sat:
            is_sat = True
            gas += 10000
            self.solver.pop()
            self.solver.push()
            self.solver.add(self.gas > gas)
        self.solver.pop()
        self.solver.push()
        self.solver.add(self.gas > gas - 10000)
        if self.solver.check() == sat:
            self.model = self.solver.model()
            return True
        else:
            if is_sat:
                raise ValueError('Solver Error')
            else:
                return False

    def assign_model(self, variables: Variables) -> int:
        # logging.debug('Assign model into cfg...')
        gas = 0
        state = State()
        for node in self.path:
            for opcode in node.opcodes:
                gas += state.simulate_with_model(opcode, self.model, variables)
        self.model_gas = gas