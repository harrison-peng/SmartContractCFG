import sha3
from math import log
from typing import Any
from src.z3_func import *
from src.gas_price import gas_table
from src.settings import *
from src.Opcode import Opcode
from src.SimulationResult import SimularionResult
from src.Variable import Variable, Variables

class State:

    def __init__(self):
        self.stack = dict()
        self.memory = dict()
        self.storage = dict()
        self.solver = Solver()
        self.msize = 0

    def simulate(self, opcode: Opcode, variables: Variables) -> SimularionResult:
        from src.Result import Result
        result = SimularionResult()

        if opcode.name in ['INVALID', 'STOP', 'REVERT', 'JUMPDEST']:
            pass
        elif opcode.name == 'TIMESTAMP':
            time_var = variables.get_variable(Variable('It_%s' % opcode.pc, 'TIMESTAMP', BitVec('It_%s' % opcode.pc, 256)))
            result.add_path_constraint(ULT(time_var, UNSIGNED_BOUND_NUMBER))

            self.stack[str(len(self.stack))] = time_var
            result.set_gas(gas_table[opcode.name])
        elif opcode.name == 'ADD':
            if len(self.stack) > 1:
                first = self.stack.pop(str(len(self.stack) - 1))
                second = self.stack.pop(str(len(self.stack) - 1))

                if isinstance(first, int) and first == 0:
                    computed = second
                elif isinstance(second, int) and second == 0:
                    computed = first
                elif is_real(first) and is_symbolic(second):
                    first = BitVecVal(first, 256)
                    computed = first + second
                elif is_symbolic(first) and is_real(second):
                    second = BitVecVal(second, 256)
                    computed = first + second
                else:
                    # computed = (first + second) % (2 ** 256)
                    computed = first + second

                self.stack[str(len(self.stack))] = computed
                result.set_gas(gas_table[opcode.name])
            else:
                raise ValueError('STACK underflow')
        elif opcode.name == 'MUL':
            if len(self.stack) > 1:
                first = self.stack.pop(str(len(self.stack) - 1))
                second = self.stack.pop(str(len(self.stack) - 1))

                if is_real(first) and is_symbolic(second):
                    first = BitVecVal(first, 256)
                elif is_symbolic(first) and is_real(second):
                    second = BitVecVal(second, 256)
                computed = first * second #& UNSIGNED_BOUND_NUMBER
                # computed = simplify(computed) if is_expr(computed) else computed

                self.stack[str(len(self.stack))] = computed
                result.set_gas(gas_table[opcode.name])
            else:
                raise ValueError('STACK underflow')
        elif opcode.name == 'SUB':
            if len(self.stack) > 1:
                first = self.stack.pop(str(len(self.stack) - 1))
                second = self.stack.pop(str(len(self.stack) - 1))

                if is_real(first) and is_symbolic(second):
                    first = BitVecVal(first, 256)
                    computed = first - second
                elif is_symbolic(first) and is_real(second):
                    second = BitVecVal(second, 256)
                    computed = first - second
                else:
                    # computed = (first - second) % (2 ** 256)
                    computed = first - second
                # computed = simplify(computed) if is_expr(computed) else computed

                self.stack[str(len(self.stack))] = computed
                result.set_gas(gas_table[opcode.name])
            else:
                raise ValueError('STACK underflow')
        elif opcode.name == 'DIV':
            if len(self.stack) > 1:
                first = self.stack.pop(str(len(self.stack) - 1))
                second = self.stack.pop(str(len(self.stack) - 1))

                if is_all_real(first, second):
                    computed = 0 if second == 0 else to_unsigned(first) // to_unsigned(second)
                else:
                    computed =first / second if is_real(second) else self.__get_if_expression(second == 0, 0, first/second)
                # computed = simplify(computed) if is_expr(computed) else computed

                self.stack[str(len(self.stack))] = computed
                result.set_gas(gas_table[opcode.name])
            else:
                raise ValueError('STACK underflow')
        elif opcode.name == 'SDIV':
            if len(self.stack) > 1:
                first = self.stack.pop(str(len(self.stack) - 1))
                second = self.stack.pop(str(len(self.stack) - 1))

                if is_all_real(first, second):
                    first = to_signed(first)
                    second = to_signed(second)
                    if second == 0:
                        computed = 0
                    elif first == -2**255 and second == -1:
                        computed = -2**255
                    else:
                        sign = -1 if (first / second) < 0 else 1
                        computed = sign * (abs(first) / abs(second))
                else:
                    first = to_symbolic(first)
                    second = to_symbolic(second)
                    self.solver.push()
                    self.solver.add(Not(second == 0))
                    if check_sat(solver) == unsat:
                        computed = 0
                    else:
                        self.solver.push()
                        self.solver.add(Not(And(first == -2**255, second == -1)))
                        if check_sat(self.solver) == unsat:
                            computed = -2**255
                        else:
                            self.solver.push()
                            self.solver.add(first / second < 0)
                            sign = -1 if check_sat(self.solver) == sat else 1
                            z3_abs = lambda x: self.__get_if_expression(x >= 0, x, -x)
                            first = z3_abs(first)
                            second = z3_abs(second)
                            computed = sign * (first / second)
                            self.solver.pop()
                        self.solver.pop()
                    self.solver.pop()
                # computed = simplify(computed) if is_expr(computed) else computed

                self.stack[str(len(self.stack))] = computed
                result.set_gas(gas_table[opcode.name])
            else:
                raise ValueError('STACK underflow')
        elif opcode.name == 'MOD':
            if len(self.stack) > 1:
                first = self.stack.pop(str(len(self.stack) - 1))
                second = self.stack.pop(str(len(self.stack) - 1))

                if is_all_real(first, second):
                    if second == 0:
                        computed = 0
                    else:
                        first = to_unsigned(first)
                        second = to_unsigned(second)
                        computed = first % second #& UNSIGNED_BOUND_NUMBER

                else:
                    first = to_symbolic(first)
                    second = to_symbolic(second)

                    self.solver.push()
                    self.solver.add(Not(second == 0))
                    if check_sat(self.solver) == unsat:
                        # it is provable that second is indeed equal to zero
                        computed = 0
                    else:
                        computed = URem(first, second)
                    self.solver.pop()
                # computed = simplify(computed) if is_expr(computed) else computed

                self.stack[str(len(self.stack))] = computed
                result.set_gas(gas_table[opcode.name])
            else:
                raise ValueError('STACK underflow')
        elif opcode.name == 'SMOD':
            if len(self.stack) > 1:
                first = self.stack.pop(str(len(self.stack) - 1))
                second = self.stack.pop(str(len(self.stack) - 1))

                if is_all_real(first, second):
                    if second == 0:
                        computed = 0
                    else:
                        first = to_signed(first)
                        second = to_signed(second)
                        sign = -1 if first < 0 else 1
                        computed = sign * (abs(first) % abs(second))
                else:
                    first = to_symbolic(first)
                    second = to_symbolic(second)

                    self.solver.push()
                    self.solver.add(Not(second == 0))
                    if check_sat(self.solver) == unsat:
                        # NOTE: it is provable that second is indeed equal to zero
                        computed = 0
                    else:

                        self.solver.push()
                        self.solver.add(first < 0)  # check sign of first element
                        sign = BitVecVal(-1, 256) if check_sat(self.solver) == sat \
                            else BitVecVal(1, 256)
                        self.solver.pop()

                        z3_abs = lambda x: self.__get_if_expression(x >= 0, x, -x)
                        first = z3_abs(first)
                        second = z3_abs(second)

                        computed = sign * (first % second)
                    self.solver.pop()

                # computed = simplify(computed) if is_expr(computed) else computed

                self.stack[str(len(self.stack))] = computed
                result.set_gas(gas_table[opcode.name])
            else:
                raise ValueError('STACK underflow')
        elif opcode.name == 'ADDMOD':
            if len(self.stack) > 2:
                first = self.stack.pop(str(len(self.stack) - 1))
                second = self.stack.pop(str(len(self.stack) - 1))
                third = self.stack.pop(str(len(self.stack) - 1))

                if is_all_real(first, second, third):
                    if third == 0:
                        computed = 0
                    else:
                        computed = (first + second) % third
                else:
                    first = to_symbolic(first)
                    second = to_symbolic(second)
                    self.solver.push()
                    self.solver.add( Not(third == 0) )
                    if check_sat(self.solver) == unsat:
                        computed = 0
                    else:
                        first = ZeroExt(256, first)
                        second = ZeroExt(256, second)
                        third = ZeroExt(256, third)
                        computed = (first + second) % third
                        computed = Extract(255, 0, computed)
                    self.solver.pop()
                # computed = simplify(computed) if is_expr(computed) else computed

                self.stack[str(len(self.stack))] = computed
                result.set_gas(gas_table[opcode.name])
            else:
                raise ValueError('STACK underflow')
        elif opcode.name == 'MULMOD':
            if len(self.stack) > 2:
                first = self.stack.pop(str(len(self.stack) - 1))
                second = self.stack.pop(str(len(self.stack) - 1))
                third = self.stack.pop(str(len(self.stack) - 1))

                if is_all_real(first, second, third):
                    if third == 0:
                        computed = 0
                    else:
                        computed = (first * second) % third
                else:
                    first = to_symbolic(first)
                    second = to_symbolic(second)
                    self.solver.push()
                    self.solver.add( Not(third == 0) )
                    if check_sat(solver) == unsat:
                        computed = 0
                    else:
                        first = ZeroExt(256, first)
                        second = ZeroExt(256, second)
                        third = ZeroExt(256, third)
                        computed = URem(first * second, third)
                        computed = Extract(255, 0, computed)
                    self.solver.pop()
                # computed = simplify(computed) if is_expr(computed) else computed

                self.stack[str(len(self.stack))] = computed
                result.set_gas(gas_table[opcode.name])
            else:
                raise ValueError('STACK underflow')
        elif opcode.name == 'EXP':
            if len(self.stack) > 1:
                base = self.stack.pop(str(len(self.stack) - 1))
                exponent = self.stack.pop(str(len(self.stack) - 1))

                computed = 0
                if is_all_real(base, exponent):
                    computed = pow(base, exponent, 2 ** 256)

                    # NOTE: GAS
                    gas = 10 if computed == 0 else 10 + 10 * (1 + math.log(computed, 256))
                else:
                    computed = variables.get_variable(Variable('Iexp_%s', 'EXP(%s, %s)' % (self.to_string(base), self.to_string(exponent)), BitVec('Iexp_%s' % opcode.pc, 256)))
                    result.add_path_constraint(ULT(computed, UNSIGNED_BOUND_NUMBER))

                    # NOTE: GAS
                    if is_real(computed):
                        gas = 10 + 10 * (1 + math.log(computed, 256))
                    else:
                        if isinstance(base, int) and base == 256:
                            gas = simplify(10 + (10 * (1 + BV2Int(exponent)))) if is_bv(exponent) else simplify(10 + (10 * (1 + exponent)))
                        else:
                            gas_var = variables.get_variable(Variable('log_%s' % opcode.pc, 'log256(%s)' % self.to_string(computed), BitVec('log_%s' % opcode.pc, 256)))
                            gas = simplify(10 + (10 * (1 + BV2Int(gas_var))))
                            result.add_path_constraint(ULT(gas_var, UNSIGNED_BOUND_NUMBER))

                self.stack[str(len(self.stack))] = computed
                result.set_gas(gas)
            else:
                raise ValueError('STACK underflow')
        elif opcode.name == 'SIGNEXTEND':
            if len(self.stack) > 1:
                bit = self.stack.pop(str(len(self.stack) - 1))
                second = self.stack.pop(str(len(self.stack) - 1))

                if is_all_real(bit, second):
                    if bit >= 32 or bit < 0:
                        computed = second
                    else:
                        signbit_index_from_right = 8 * bit + 7
                        if second & (1 << signbit_index_from_right):
                            computed = second | (2 ** 256 - (1 << signbit_index_from_right))
                        else:
                            computed = second & ((1 << signbit_index_from_right) - 1)
                else:
                    bit = to_symbolic(bit)
                    second = to_symbolic(second)
                    self.solver.push()
                    self.solver.add(Not(Or(bit >= 32, bit < 0)))
                    if check_sat(self.solver) == unsat:
                        computed = second
                    else:
                        signbit_index_from_right = 8 * bit + 7
                        self.solver.push()
                        self.solver.add(second & (1 << signbit_index_from_right) == 0)
                        if check_sat(self.solver) == unsat:
                            computed = second | (2 ** 256 - (1 << signbit_index_from_right))
                        else:
                            computed = second & ((1 << signbit_index_from_right) - 1)
                        self.solver.pop()
                    self.solver.pop()
                # computed = simplify(computed) if is_expr(computed) else computed
                
                self.stack[str(len(self.stack))] = computed
                result.set_gas(gas_table[opcode.name])
            else:
                raise ValueError('STACK underflow')
        elif opcode.name == 'LT':
            if len(self.stack) > 1:
                first = self.stack.pop(str(len(self.stack) - 1))
                second = self.stack.pop(str(len(self.stack) - 1))

                if first == second:
                    computed = 0
                else:
                    if is_all_real(first, second):
                        first = to_unsigned(first)
                        second = to_unsigned(second)
                        computed = 1 if first < second else 0
                    else:
                        computed = self.__get_if_expression(ULT(first, second), BitVecVal(1, 256), BitVecVal(0, 256))
                    # computed = simplify(computed) if is_expr(computed) else computed

                self.stack[str(len(self.stack))] = computed
                result.set_gas(gas_table[opcode.name])
            else:
                raise ValueError('STACK underflow')
        elif opcode.name == 'GT':
            if len(self.stack) > 1:
                first = self.stack.pop(str(len(self.stack) - 1))
                second = self.stack.pop(str(len(self.stack) - 1))

                if is_all_real(first, second):
                    first = to_unsigned(first)
                    second = to_unsigned(second)
                    computed = 1 if first > second else 0
                else:
                    computed = self.__get_if_expression(UGT(first, second), BitVecVal(1, 256), BitVecVal(0, 256))
                # computed = simplify(computed) if is_expr(computed) else computed

                self.stack[str(len(self.stack))] = computed
                result.set_gas(gas_table[opcode.name])
            else:
                raise ValueError('STACK underflow')
        elif opcode.name == 'SLT':
            if len(self.stack) > 1:
                first = self.stack.pop(str(len(self.stack) - 1))
                second = self.stack.pop(str(len(self.stack) - 1))

                if is_all_real(first, second):
                    first = to_signed(first)
                    second = to_signed(second)
                    computed = 1 if first < second else 0
                else:
                    computed = self.__get_if_expression(first < second, BitVecVal(1, 256), BitVecVal(0, 256))
                # computed = simplify(computed) if is_expr(computed) else computed

                self.stack[str(len(self.stack))] = computed
                result.set_gas(gas_table[opcode.name])
            else:
                raise ValueError('STACK underflow')
        elif opcode.name == 'SGT':
            if len(self.stack) > 1:
                first = self.stack.pop(str(len(self.stack) - 1))
                second = self.stack.pop(str(len(self.stack) - 1))

                if is_all_real(first, second):
                    first = to_signed(first)
                    second = to_signed(second)
                    computed = 1 if first > second else 0
                else:
                    computed = self.__get_if_expression(first > second, BitVecVal(1, 256), BitVecVal(0, 256))
                # computed = simplify(computed) if is_expr(computed) else computed

                self.stack[str(len(self.stack))] = computed
                result.set_gas(gas_table[opcode.name])
            else:
                raise ValueError('STACK underflow')
        elif opcode.name == 'EQ':
            if len(self.stack) > 1:
                first = self.stack.pop(str(len(self.stack) - 1))
                second = self.stack.pop(str(len(self.stack) - 1))

                if is_all_real(first, second):
                    computed = 1 if first == second else 0
                else:
                    computed = self.__get_if_expression(first == second, BitVecVal(1, 256), BitVecVal(0, 256))
                # computed = simplify(computed) if is_expr(computed) else computed

                self.stack[str(len(self.stack))] = computed
                result.set_gas(gas_table[opcode.name])
            else:
                raise ValueError('STACK underflow')
        elif opcode.name == 'ISZERO':
            if len(self.stack) > 0:
                first = self.stack.pop(str(len(self.stack) - 1))

                if is_real(first):
                    computed = 1 if first == 0 else 0
                else:
                    condiiton = first.decl().name() == 'if' and str(first.arg(1)) in ['1', '0'] and str(first.arg(2)) in ['1', '0']
                    computed = self.__get_if_expression(first.arg(0), first.arg(2), first.arg(1)) if condiiton else self.__get_if_expression(first == 0, BitVecVal(1, 256), BitVecVal(0, 256))
                # computed = simplify(computed) if is_expr(computed) else computed

                self.stack[str(len(self.stack))] = computed
                result.set_gas(gas_table[opcode.name])
            else:
                raise ValueError('STACK underflow')
        elif opcode.name == 'AND':
            if len(self.stack) > 1:
                first = self.stack.pop(str(len(self.stack) - 1))
                second = self.stack.pop(str(len(self.stack) - 1))

                if isinstance(first, int) and first == 1461501637330902918203684832716283019655932542975:
                    computed = second
                    if is_expr(second):
                        result.add_path_constraint(ULT(computed, ADDRESS_BOUND_NUMBER))
                elif isinstance(second, int) and second == 1461501637330902918203684832716283019655932542975:
                    computed = first
                    if is_expr(first):
                        result.add_path_constraint(ULT(computed, ADDRESS_BOUND_NUMBER))
                elif isinstance(first, int) and first == 115792089237316195423570985008687907853269984665640564039457584007913129639935:
                    computed = second
                elif isinstance(second, int) and second == 115792089237316195423570985008687907853269984665640564039457584007913129639935:
                    computed = first
                else:
                    computed = first & second
                    # computed = simplify(computed) if is_expr(computed) else computed

                self.stack[str(len(self.stack))] = computed
                result.set_gas(gas_table[opcode.name])
            else:
                raise ValueError('STACK underflow')
        elif opcode.name == 'OR':
            if len(self.stack) > 1:
                first = self.stack.pop(str(len(self.stack) - 1))
                second = self.stack.pop(str(len(self.stack) - 1))

                computed = first | second
                # computed = simplify(computed) if is_expr(computed) else computed

                self.stack[str(len(self.stack))] = computed
                result.set_gas(gas_table[opcode.name])
            else:
                raise ValueError('STACK underflow')
        elif opcode.name == 'XOR':
            if len(self.stack) > 1:
                first = self.stack.pop(str(len(self.stack) - 1))
                second = self.stack.pop(str(len(self.stack) - 1))

                computed = first ^ second
                # computed = simplify(computed) if is_expr(computed) else computed

                self.stack[str(len(self.stack))] = computed
                result.set_gas(gas_table[opcode.name])
            else:
                raise ValueError('STACK underflow')
        elif opcode.name == 'NOT':
            if len(self.stack) > 0:
                first = self.stack.pop(str(len(self.stack) - 1))

                computed = (~first) & UNSIGNED_BOUND_NUMBER
                # computed = simplify(computed) if is_expr(computed) else computed

                self.stack[str(len(self.stack))] = computed
                result.set_gas(gas_table[opcode.name])
            else:
                raise ValueError('STACK underflow')
        elif opcode.name == 'BYTE':
            if len(self.stack) > 1:
                first = self.stack.pop(str(len(self.stack) - 1))
                second = self.stack.pop(str(len(self.stack) - 1))
                byte_index = 32 - first - 1

                if is_all_real(first, second):
                    if first >= 32 or first < 0:
                        computed = 0
                    else:
                        computed = second & (255 << (8 * byte_index))
                        computed >>= (8 * byte_index)
                else:
                    first = to_symbolic(first)
                    second = to_symbolic(second)
                    self.solver.push()
                    self.solver.add(Not(Or(first >= 32, first < 0)))
                    if check_sat(self.solver) == unsat:
                        computed = 0
                    else:
                        computed = second & (255 << (8 * byte_index))
                        computed >>= (8 * byte_index)
                    self.solver.pop()
                # computed = simplify(computed) if is_expr(computed) else computed

                self.stack[str(len(self.stack))] = computed
                result.set_gas(gas_table[opcode.name])
            else:
                raise ValueError('STACK underflow')
        elif opcode.name in ['SHA3', 'KECCAK256']:
            if len(self.stack) > 1:
                position = self.stack.pop(str(len(self.stack) - 1))
                length = self.stack.pop(str(len(self.stack) - 1))

                if isinstance(position, int) and isinstance(length, int):
                    mem_num = length//32
                    data = 0

                    for i in range(mem_num):
                        if (position + 32*i) in self.memory.keys():
                            if isinstance(self.memory[position + 32*i], int):
                                if self.memory[position + 32*i] != 0:
                                    data += self.memory[position + 32*i]
                            else:
                                data += self.memory[position + 32 * i]
                                # data = simplify(data) if is_expr(data) else data
                        else:
                            mem_var = variables.get_variable(Variable('Imem_%s' % opcode.pc, 'memory[%s:%s+32]' % (self.to_string(i), self.to_string(i)), BitVec('Imem_%s' % opcode.pc, 256)))
                            data = data + mem_var
                            result.add_path_constraint(ULT(mem_var, UNSIGNED_BOUND_NUMBER))
                            result.add_path_constraint(ULT(data, UNSIGNED_BOUND_NUMBER))
                else:
                    data = variables.get_variable(Variable('Isha3_%s' % opcode.pc, 'SHA3(memory[%s:%s])' % (self.to_string(position), self.to_string(position + length)), BitVec('Isha3_%s' % opcode.pc, 256)))
                    result.add_path_constraint(ULT(data, UNSIGNED_BOUND_NUMBER))

                if isinstance(data, int):
                    computed = int(sha3.sha3_224(str(data).encode('utf-8')).hexdigest(), 16)
                else:
                    computed = variables.get_variable(Variable('Isha3_%s' % opcode.pc, 'SHA3(%s)' % self.to_string(data), BitVec('Isha3_%s' % opcode.pc, 256)))
                    result.add_path_constraint(ULT(computed, UNSIGNED_BOUND_NUMBER))
                # data = simplify(data) if is_expr(data) else data

                self.stack[str(len(self.stack))] = computed

                # NOTE: GAS
                if isinstance(length, int):
                    gas = 30 + 6 * (length/32)
                else:
                    if str(data) == 'Ia_caller':
                        gas = 150
                    else:
                        size_var = variables.get_variable(Variable('Isize_%s' % opcode.pc, 'The word size of %s' % self.to_string(data), BitVec('Isize_%s' % opcode.pc, 256)))
                        result.add_path_constraint(ULT(size_var, BYTE_BOUND_NUMBER))
                        gas = simplify(30 + 6 * BV2Int(size_var))

                result.set_gas(gas)
            else:
                raise ValueError('STACK underflow')
        elif opcode.name == 'ADDRESS':
            addr_var = variables.get_variable(Variable('Ia', 'address(this) (address of the executing contract)', BitVec('Ia', 256)))
            result.add_path_constraint(ULT(addr_var, UNSIGNED_BOUND_NUMBER))

            self.stack[str(len(self.stack))] = addr_var
            result.set_gas(gas_table[opcode.name])
        elif opcode.name == 'BALANCE':
            if len(self.stack) > 0:
                address = self.stack.pop(str(len(self.stack) - 1))

                banlance_var = variables.get_variable(Variable('Ibalance_%s' % opcode.pc, 'address(%s).balance' % self.to_string(address), BitVec('Ibalance_%s' % opcode.pc, 256)))
                result.add_path_constraint(ULT(banlance_var, UNSIGNED_BOUND_NUMBER))

                self.stack[str(len(self.stack))] = banlance_var
                result.set_gas(gas_table[opcode.name])
            else:
                raise ValueError('STACK underflow')
        elif opcode.name == 'CALLER':
            caller_var = variables.get_variable(Variable('Ia_caller', 'msg.caller (caller address)', BitVec('Ia_caller', 256)))
            result.add_path_constraint(ULT(caller_var, UNSIGNED_BOUND_NUMBER))

            self.stack[str(len(self.stack))] = caller_var
            result.set_gas(gas_table[opcode.name])
        elif opcode.name == 'ORIGIN':
            origin_var = variables.get_variable(Variable('Io_%s' % opcode.pc, 'tx.origin (transaction origin address)', BitVec('Io_%s' % opcode.pc, 256)))
            result.add_path_constraint(ULT(origin_var, UNSIGNED_BOUND_NUMBER))

            self.stack[str(len(self.stack))] = origin_var
            result.set_gas(gas_table[opcode.name])
        elif opcode.name == 'CALLVALUE':
            value_var = variables.get_variable(Variable('Iv', 'tx.origin (transaction origin address)', BitVec('Iv', 256)))
            result.add_path_constraint(ULT(value_var, UNSIGNED_BOUND_NUMBER))

            self.stack[str(len(self.stack))] = value_var
            result.set_gas(gas_table[opcode.name])
        elif opcode.name == 'CALLDATALOAD':
            if len(self.stack) > 0:
                position = self.stack.pop(str(len(self.stack) - 1))

                # NOTE: Check if the sym var of msg.data is already created or not
                if isinstance(position, int):
                    data_var = variables.get_variable(Variable('Id_%s' % opcode.pc, 'msg.data[%s:%s]' % (self.to_string(position), self.to_string(position + 32)), BitVec('Id_%s' % opcode.pc, 256)))
                else:
                    data_var = variables.get_variable(Variable('Id_%s' % opcode.pc, 'msg.data[%s:%s]' % (self.to_string(position), self.to_string(simplify(position+32))), BitVec('Id_%s' % opcode.pc, 256)))
                result.add_path_constraint(ULT(data_var, UNSIGNED_BOUND_NUMBER))

                self.stack[str(len(self.stack))] = data_var
                result.set_gas(gas_table[opcode.name])
            else:
                raise ValueError('STACK underflow')
        elif opcode.name == 'CALLDATASIZE':
            ds_var = variables.get_variable(Variable('Id_size', 'msg.data.size', BitVec('Id_size', 256)))
            result.add_path_constraint(ULT(ds_var, BYTE_BOUND_NUMBER))

            self.stack[str(len(self.stack))] = ds_var
            result.set_gas(gas_table[opcode.name])
        elif opcode.name == "CALLDATACOPY":
            if len(self.stack) > 2:
                mem_p = self.stack.pop(str(len(self.stack) - 1))
                msg_p = self.stack.pop(str(len(self.stack) - 1))
                num_bytes = self.stack.pop(str(len(self.stack) - 1))

                data_var = variables.get_variable(Variable('Id_%s' % opcode.pc, 'msg.data[%s:%s+%s]' % (msg_p, msg_p, num_bytes), BitVec('Id_%s' % opcode.pc, 256)))
                result.add_path_constraint(ULT(data_var, UNSIGNED_BOUND_NUMBER))
                self.memory[mem_p] = data_var
                
                if isinstance(self.msize, int) and isinstance(mem_p, int):
                    old_msize = self.msize
                    self.msize = mem_p if mem_p > self.msize else self.msize
                else:
                    old_msize = BV2Int(self.msize) if isinstance(self.msize, BitVecRef) else self.msize
                    mem_p = BV2Int(mem_p) if isinstance(mem_p, BitVecRef) else mem_p
                    self.msize = self.__get_if_expression(mem_p > self.msize, mem_p, self.msize)

                # NOTE: GAS
                if is_real(num_bytes):
                    gas = 2 + 3 * (num_bytes / 32)
                else:
                    ws_var = variables.get_variable(Variable('Isize_%s' % opcode.pc, 'The word size of %s' % self.to_string(num_bytes), BitVec('Isize_%s' % opcode.pc, 256)))
                    result.add_path_constraint(ULT(ws_var, BYTE_BOUND_NUMBER))
                    gas = simplify(2 + 3 * BV2Int(ws_var))
                result.set_gas(gas)
                result.set_memory_gas(3 * (self.msize - old_msize) + (self.msize * self.msize)/512 - (old_msize * old_msize)/512)
            else:
                raise ValueError('STACK underflow')
        elif opcode.name == 'CODESIZE':
            size_var = variables.get_variable(Variable('Id_size', 'address(this).code.size', BitVec('Id_size', 256)))
            result.add_path_constraint(ULT(size_var, BYTE_BOUND_NUMBER))

            self.stack[str(len(self.stack))] = size_var
            result.set_gas(gas_table[opcode.name])
        elif opcode.name == 'CODECOPY':
            if len(self.stack) > 2:
                mem_p = self.stack.pop(str(len(self.stack) - 1))
                msg_p = self.stack.pop(str(len(self.stack) - 1))
                num_bytes = self.stack.pop(str(len(self.stack) - 1))

                code_var = variables.get_variable(Variable('Ic_%s' % opcode.pc, 'address(this).code[%s:%s]' % (self.to_string(mem_p), self.to_string(msg_p+num_bytes)), BitVec('Ic_%s' % opcode.pc, 256)))
                result.add_path_constraint(ULT(code_var, UNSIGNED_BOUND_NUMBER))
                self.memory[mem_p] = code_var

                if isinstance(self.msize, int) and isinstance(mem_p, int):
                    old_msize = self.msize
                    self.msize = mem_p if mem_p > self.msize else self.msize
                else:
                    old_msize = BV2Int(self.msize) if isinstance(self.msize, BitVecRef) else self.msize
                    mem_p = BV2Int(mem_p) if isinstance(mem_p, BitVecRef) else mem_p
                    self.msize = self.__get_if_expression(mem_p > self.msize, mem_p, self.msize)

                # NOTE: GAS
                if is_real(num_bytes):
                    gas = 2 + 3 * (num_bytes / 32)
                else:
                    size_var = variables.get_variable(Variable('Isize_%s' % str(num_bytes).split('_')[1], 'The word size of %s' % self.to_string(num_bytes), BitVec('Isize_%s' % str(num_bytes).split('_')[1], 256)))
                    result.add_path_constraint(ULT(size_var, BYTE_BOUND_NUMBER))

                    gas = simplify(30 + 6 * BV2Int(size_var))
                result.set_gas(gas)
                result.set_memory_gas(3 * (self.msize - old_msize) + (self.msize * self.msize)/512 - (old_msize * old_msize)/512)
            else:
                raise ValueError('STACK underflow')
        elif opcode.name == 'GASPRICE':
            gas_var = variables.get_variable(Variable('Ip_%s' % opcode.pc, 'tx.gasprice', BitVec('Ip_%s' % opcode.pc, 256)))
            result.add_path_constraint(ULT(gas_var, UNSIGNED_BOUND_NUMBER))

            self.stack[str(len(self.stack))] = gas_var
            result.set_gas(gas_table[opcode.name])
        elif opcode.name == 'RETURNDATACOPY':
            if len(self.stack) > 2:
                z = self.stack.pop(str(len(self.stack) - 1))
                y = self.stack.pop(str(len(self.stack) - 1))
                x = self.stack.pop(str(len(self.stack) - 1))

                data_var = variables.get_variable(Variable('Id_%s'% opcode.pc, 'RETURNDATA[%s:%s]' % (self.to_string(y), self.to_string(y+x)), BitVec('Id_%s'% opcode.pc, 256)))
                result.add_path_constraint(ULT(data_var, UNSIGNED_BOUND_NUMBER))
                self.memory[z] = data_var

                if isinstance(self.msize, int) and isinstance(z, int):
                    old_msize = self.msize
                    self.msize = z if z > self.msize else self.msize
                else:
                    old_msize = BV2Int(self.msize) if isinstance(self.msize, BitVecRef) else self.msize
                    z = BV2Int(z) if isinstance(z, BitVecRef) else z
                    self.msize = self.__get_if_expression(z > self.msize, z, self.msize)

                # NOTE: GAS
                if is_real(x):
                    gas = 2 + 3 * (x / 32)
                else:
                    size_var = variables.get_variable(Variable('Isize_%s' % str(x).split('_')[1], 'The word size of %s' % self.to_string(x), BitVec('Isize_%s' % str(x).split('_')[1], 256)))
                    result.add_path_constraint(ULT(size_var, BYTE_BOUND_NUMBER))
                    gas = simplify(30 + 6 * BV2Int(size_var))
                result.set_gas(gas)
                result.set_memory_gas(3 * (self.msize - old_msize) + (self.msize * self.msize)/512 - (old_msize * old_msize)/512)
            else:
                raise ValueError('STACK underflow')
        elif opcode.name == 'RETURNDATASIZE':
            size_var = variables.get_variable(Variable('Id_size', 'data.size', BitVec('Id_size', 256)))
            result.add_path_constraint(ULT(size_var, BYTE_BOUND_NUMBER))

            self.stack[str(len(self.stack))] = size_var
            result.set_gas(gas_table[opcode.name])
        elif opcode.name == 'NUMBER':
            number_var = variables.get_variable(Variable('Iblocknum', 'block.number', BitVec('Iblocknum', 256)))
            result.add_path_constraint(ULT(number_var, BYTE_BOUND_NUMBER))

            self.stack[str(len(self.stack))] = number_var
            result.set_gas(gas_table[opcode.name])
        elif opcode.name == 'POP':
            if len(self.stack) > 0:
                self.stack.pop(str(len(self.stack) - 1))
                result.set_gas(gas_table[opcode.name])
            else:
                raise ValueError('STACK underflow')
        elif opcode.name == 'MLOAD':
            if len(self.stack) > 0:
                address = self.stack.pop(str(len(self.stack) - 1))
                value = self.memory.get(address, None)

                if value is None:
                    value = self.__get_if_expression(self.memory == list(self.memory.keys())[0], self.memory[list(self.memory.keys())[0]], BitVecVal(0, 256))
                    if len(self.memory) > 1:
                        tem_val = value
                        for key, val in self.memory.items():
                            value = self.__get_if_expression(address == key, val, tem_val)
                            tem_val = value
                    value_s = simplify(value) if is_expr(value) else value
                    value = value_s.as_long() if isinstance(value_s, BitVecNumRef) else value

                self.stack[str(len(self.stack))] = value
                result.set_gas(gas_table[opcode.name])
            else:
                raise ValueError('STACK underflow')
        elif opcode.name == 'MSTORE':
            if len(self.stack) > 1:
                address = self.stack.pop(str(len(self.stack) - 1))
                value = self.stack.pop(str(len(self.stack) - 1))
                if not (isinstance(value, int) and value == 0):
                    self.memory[address] = value

                if isinstance(self.msize, int) and isinstance(address, int):
                    old_msize = self.msize
                    self.msize = address if address > self.msize else self.msize
                else:
                    old_msize = BV2Int(self.msize) if isinstance(self.msize, BitVecRef) else self.msize
                    address = BV2Int(address) if isinstance(address, BitVecRef) else address
                    self.msize = self.__get_if_expression(address > self.msize, address, self.msize)

                result.set_gas(gas_table[opcode.name])
                result.set_memory_gas(3 * (self.msize - old_msize) + (self.msize * self.msize)/512 - (old_msize * old_msize)/512)
            else:
                raise ValueError('STACK underflow')
        elif opcode.name == 'MSTORE8':
            if len(self.stack) > 1:
                address = self.stack.pop(str(len(self.stack) - 1))
                value = self.stack.pop(str(len(self.stack) - 1))

                if isinstance(value, int):
                    self.memory[address] = value & 0xFF
                else:
                    memory_var = variables.get_variable(Variable('Imem_%s' % opcode.pc, '%s & 0xFF', BitVec('Imem_%s' % opcode.pc, 256)))
                    result.add_path_constraint(ULT(memory_var, 255))
                    self.memory[address] = memory_var
                
                if isinstance(self.msize, int) and isinstance(address, int):
                    old_msize = self.msize
                    self.msize = address if address > self.msize else self.msize
                else:
                    old_msize = BV2Int(self.msize) if isinstance(self.msize, BitVecRef) else self.msize
                    address = BV2Int(address) if isinstance(address, BitVecRef) else address
                    self.msize = self.__get_if_expression(address > self.msize, address, self.msize)

                result.set_gas(gas_table[opcode.name])
                result.set_memory_gas(3 * (self.msize - old_msize) + (self.msize * self.msize)/512 - (old_msize * old_msize)/512)
            else:
                raise ValueError('STACK underflow')
        elif opcode.name == 'SLOAD':
            if len(self.stack) > 0:
                address = self.stack.pop(str(len(self.stack) - 1))

                if len(self.storage) == 0:
                    # value = 0
                    value = variables.get_variable(Variable('Isto_%s' % opcode.pc, 'storage[%s]' % self.to_string(address), BitVec('Isto_%s' % opcode.pc, 256)))
                    result.add_path_constraint(ULT(value, UNSIGNED_BOUND_NUMBER))
                else:
                    value = self.storage.get(str(address), None)

                    if value is None:
                        value = variables.get_variable(Variable('Isto_%s' % opcode.pc, 'storage[%s]' % self.to_string(address), BitVec('Isto_%s' % opcode.pc, 256)))
                        result.add_path_constraint(ULT(value, UNSIGNED_BOUND_NUMBER))

                self.stack[str(len(self.stack))] = value
                result.set_gas(gas_table[opcode.name])
            else:
                raise ValueError('STACK underflow')
        elif opcode.name == 'SSTORE':
            if len(self.stack) > 1:
                address = self.stack.pop(str(len(self.stack) - 1))
                value = self.stack.pop(str(len(self.stack) - 1))
                self.storage[address] = value

                # NOTE: GAS
                if len(self.storage) == 0:
                    if isinstance(value, int):
                        if value == 0:
                            gas = 5000
                        else:
                            gas = 20000
                    else:
                        gas = simplify(BV2Int(self.__get_if_expression(Not(value == 0), BitVecVal(20000, 256), BitVecVal(5000, 256))))
                else:
                    if address in self.storage.keys():
                        gas = 5000
                    else:
                        if value == 0:
                            gas = 5000
                        else:
                            cond = False
                            for k in [e for e in self.storage.keys() if is_expr(e)]:
                                cond = Or(cond, k == address)
                            gas = simplify(BV2Int(self.__get_if_expression(Or(value == 0, cond), BitVecVal(5000, 256), BitVecVal(20000, 256))))
                result.set_gas(gas)
            else:
                raise ValueError('STACK underflow')
        elif opcode.name == 'JUMP':
            if len(self.stack) > 0:
                result.set_jump_tag(self.stack.pop(str(len(self.stack) - 1)))
                result.set_gas(gas_table[opcode.name])
            else:
                raise ValueError('STACK underflow')
        elif opcode.name == 'JUMPI':
            if len(self.stack) > 1:
                result.set_jump_tag(self.stack.pop(str(len(self.stack) - 1)))
                result.set_jump_condition(self.stack.pop(str(len(self.stack) - 1)))
                result.set_gas(gas_table[opcode.name])
            else:
                raise ValueError('STACK underflow')
        elif opcode.name == 'GAS':
            gas_var = variables.get_variable(Variable('Igas_%s' % opcode.pc, 'Gas Remaining', BitVec('Igas_%s' % opcode.pc, 256)))
            result.add_path_constraint(ULT(gas_var, UNSIGNED_BOUND_NUMBER))

            self.stack[str(len(self.stack))] = gas_var
            result.set_gas(gas_table[opcode.name])
        elif opcode.name.startswith('PUSH', 0):
            if opcode.name == 'PUSHDEPLOYADDRESS':
                pushed_value = variables.get_variable(Variable('Iaddr_%s' % opcode.pc, 'address(deployed)', BitVec('Iaddr_%s' % opcode.pc, 256)))
                result.add_path_constraint(ULT(pushed_value, UNSIGNED_BOUND_NUMBER))
            else:
                pushed_value = int(str(opcode.value), 16)
            self.stack[str(len(self.stack))] = pushed_value
            result.set_gas(gas_table['PUSH'])
        elif opcode.name.startswith('DUP', 0):
            position = len(self.stack) - int(opcode.name[3:], 10)
            if position >= 0:
                duplicate_value = self.stack[str(position)]
                self.stack[str(len(self.stack))] = duplicate_value
                result.set_gas(gas_table['DUP'])
            else:
                raise ValueError('STACK underflow')
        elif opcode.name.startswith('SWAP', 0):
            position = len(self.stack) - 1 - int(opcode.name[4:], 10)
            if position >= 0:
                temp_value = self.stack[str(position)]
                self.stack[str(position)] = self.stack[str(len(self.stack) - 1)]
                self.stack[str(len(self.stack) - 1)] = temp_value
                result.set_gas(gas_table['SWAP'])
            else:
                return 'ERROR'
                # raise ValueError('STACK underflow')
        elif opcode.name in ('LOG0', 'LOG1', 'LOG2', 'LOG3', 'LOG4'):
            num_of_pops = 2 + int(opcode.name[3:])
            if len(self.stack) >= num_of_pops:
                offset = self.stack.pop(str(len(self.stack) - 1))
                word = self.stack.pop(str(len(self.stack) - 1))
                for _ in range(int(opcode.name[3:])):
                    num_of_pops -= 1
                    pop_value = self.stack.pop(str(len(self.stack) - 1))

                # NOTE: GAS
                if isinstance(word, int):
                    gas = (int(opcode.name[3:]) + 1) * 375 + (8 * (word / 32))
                else:
                    size_var = variables.get_variable(Variable('Isize_%s' % opcode.pc, 'The bytes of %s' % self.to_string(word), BitVec('Isize_%s' % opcode.pc, 256)))
                    result.add_path_constraint(ULT(size_var, BYTE_BOUND_NUMBER))
                    gas = (int(opcode.name[3:]) + 1) * 375 + (8 * BV2Int(size_var))
                result.set_gas(gas)
            else:
                raise ValueError('STACK underflow')
        elif opcode.name == 'CALL':
            if len(self.stack) > 6:
                out_gas = self.stack.pop(str(len(self.stack) - 1))
                addr = self.stack.pop(str(len(self.stack) - 1))
                out_value = self.stack.pop(str(len(self.stack) - 1))
                in_position = self.stack.pop(str(len(self.stack) - 1))
                in_length = self.stack.pop(str(len(self.stack) - 1))
                out_position = self.stack.pop(str(len(self.stack) - 1))
                out_length = self.stack.pop(str(len(self.stack) - 1))

                call_var = variables.get_variable(Variable('Icall_%s' % opcode.pc, 'call success or not', BitVec('Icall_%s' % opcode.pc, 256)))
                result.add_path_constraint(Or(call_var == 1, call_var == 0))
                self.stack[str(len(self.stack))] = call_var

                # NOTE: GAS
                # TODO: fix gas
                gas = gas_table[opcode.name]
                out_value = out_value.as_long() if isinstance(out_value, z3.z3.BitVecNumRef) else out_value
                if isinstance(out_value, int) and out_value != 0:
                    gas += 9000
                elif is_expr(out_value):
                    g = self.__get_if_expression(out_value == 0, 0, 9000)
                    if is_bv(g):
                        gas += BV2Int(self.__get_if_expression(out_value == 0, 0, 9000))
                    else:
                        gas += self.__get_if_expression(out_value == 0, 0, 9000)
                result.set_gas(gas)
            else:
                raise ValueError('STACK underflow')
        elif opcode.name == 'CALLCODE':
            if len(self.stack) > 6:
                out_gas = self.stack.pop(str(len(self.stack) - 1))
                recipient = self.stack.pop(str(len(self.stack) - 1))
                out_wei = self.stack.pop(str(len(self.stack) - 1))
                in_value = self.stack.pop(str(len(self.stack) - 1))
                in_size = self.stack.pop(str(len(self.stack) - 1))
                out_value = self.stack.pop(str(len(self.stack) - 1))
                out_size = self.stack.pop(str(len(self.stack) - 1))

                call_var = variables.get_variable(Variable('Icall_%s' % opcode.pc, 'call success or not', BitVec('Icall_%s' % opcode.pc, 256)))
                result.add_path_constraint(Or(call_var == 1, call_var == 0))
                self.stack[str(len(self.stack))] = call_var
                result.set_gas(gas_table[opcode.name])
            else:
                raise ValueError('STACK underflow')
        elif opcode.name in ['DELEGATECALL', 'STATICCALL']:
            if len(self.stack) > 2:
                out_gas = self.stack.pop(str(len(self.stack) - 1))
                recipient = self.stack.pop(str(len(self.stack) - 1))
                in_value = self.stack.pop(str(len(self.stack) - 1))
                in_size = self.stack.pop(str(len(self.stack) - 1))
                out_value = self.stack.pop(str(len(self.stack) - 1))
                out_size = self.stack.pop(str(len(self.stack) - 1))

                call_var = variables.get_variable(Variable('Icall_%s' % opcode.pc, 'call success or not', BitVec('Icall_%s' % opcode.pc, 256)))
                result.add_path_constraint(Or(call_var == 1, call_var == 0))
                self.stack[str(len(self.stack))] = call_var
                result.set_gas(gas_table[opcode.name])
            else:
                raise ValueError('STACK underflow')
        elif opcode.name == 'RETURN':
            if len(self.stack) > 1:
                offset = self.stack.pop(str(len(self.stack) - 1))
                length = self.stack.pop(str(len(self.stack) - 1))
                result.set_gas(gas_table[opcode.name])
            else:
                raise ValueError('STACK underflow')
        elif opcode.name == 'CREATE':
            if len(self.stack) > 2:
                value = self.stack.pop(str(len(self.stack) - 1))
                offset = self.stack.pop(str(len(self.stack) - 1))
                length = self.stack.pop(str(len(self.stack) - 1))

                addr_var = variables.get_variable(Variable('Iaddr_%s' % opcode.pc, 'memory[%s:%s].value(%s)' % (self.to_string(offset), self.to_string(offset + length), self.to_string(value)), BitVec('Iaddr_%s' % opcode.pc, 256)))
                result.add_path_constraint(ULT(addr_var, ADDRESS_BOUND_NUMBER))

                self.stack[str(len(self.stack))] = addr_var
                result.set_gas(gas_table[opcode.name])
            else:
                raise ValueError('STACK underflow')
        elif opcode.name == 'EXTCODESIZE':
            if len(self.stack) > 0:
                address = self.stack.pop(str(len(self.stack) - 1))

                code_var = variables.get_variable(Variable('Icodesize_%s' % opcode.pc, 'address(%s).code.size' % self.to_string(address), BitVec('Icodesize_%s' % opcode.pc, 256)))
                result.add_path_constraint(ULT(code_var, ADDRESS_BOUND_NUMBER))

                self.stack[str(len(self.stack))] = code_var
                result.set_gas(gas_table[opcode.name])
            else:
                raise ValueError('STACK underflow')
        elif opcode.name == 'BLOCKHASH':
            if len(self.stack) > 0:
                block_num = self.stack.pop(str(len(self.stack) - 1))

                hash_var = variables.get_variable(Variable('Ih_%s' % opcode.pc, 'block.blockHash(%s)' % self.to_string(block_num), BitVec('Ih_%s' % opcode.pc, 256)))
                result.add_path_constraint(ULT(hash_var, ADDRESS_BOUND_NUMBER))

                self.stack[str(len(self.stack))] = hash_var
                result.set_gas(gas_table[opcode.name])
            else:
                raise ValueError('STACK underflow')
        elif opcode.name == 'SELFDESTRUCT':
            if len(self.stack) > 0:
                address = self.stack.pop(str(len(self.stack) - 1))

                contract_var = variables.get_variable(Variable('Inewaccount_%s' % opcode.pc, 'selfdestruct(address(%s))' % self.to_string(address), BitVec('Inewaccount_%s' % opcode.pc, 256)))
                result.add_path_constraint(Or(contract_var==1, contract_var==0))
                result.set_gas(5000 + BV2Int(self.__get_if_expression(contract_var==1, BitVecVal(25000, 256), BitVecVal(0, 256))))
            else:
                raise ValueError('STACK underflow')
        elif opcode.name == 'MSIZE':
            size_var = variables.get_variable(Variable('Imemsize_%s' % opcode.pc, 'size of memory for this contract execution, in bytes', BitVec('Imemsize_%s' % opcode.pc, 256)))
            result.add_path_constraint(ULT(size_var, UNSIGNED_BOUND_NUMBER))

            self.stack[str(len(self.stack))] = size_var
            result.set_gas(gas_table[opcode.name])
        elif opcode.name == 'SHL':
            if len(self.stack) > 1:
                shift = self.stack.pop(str(len(self.stack) - 1))
                value = self.stack.pop(str(len(self.stack) - 1))

                if isinstance(shift, int) and isinstance(value, int):
                    shift_value = value << shift
                else:
                    shift_value = variables.get_variable(Variable('Ishl_%s' % opcode.pc, '%s << %s' % (self.to_string(value), self.to_string(shift)), BitVec('Ishl_%s' % opcode.pc, 256)))
                    result.add_path_constraint(ULT(shift_value, UNSIGNED_BOUND_NUMBER))
                
                self.stack[str(len(self.stack))] = shift_value
                result.set_gas(gas_table[opcode.name])
            else:
                raise ValueError('STACK underflow')
        elif opcode.name == 'SHR':
            if len(self.stack) > 1:
                shift = self.stack.pop(str(len(self.stack) - 1))
                value = self.stack.pop(str(len(self.stack) - 1))

                if isinstance(shift, int) and isinstance(value, int):
                    shift_value = value >> shift
                else:
                    shift_value = variables.get_variable(Variable('Ishr_%s' % opcode.pc, '%s >> %s' % (self.to_string(value), self.to_string(shift)), BitVec('Ishr_%s' % opcode.pc, 256)))
                    result.add_path_constraint(ULT(shift_value, UNSIGNED_BOUND_NUMBER))
                
                self.stack[str(len(self.stack))] = shift_value
                result.set_gas(gas_table[opcode.name])
            else:
                raise ValueError('STACK underflow')
        elif opcode.name == 'SAR':
            if len(self.stack) > 1:
                shift = self.stack.pop(str(len(self.stack) - 1))
                value = self.stack.pop(str(len(self.stack) - 1))

                if isinstance(shift, int) and isinstance(value, int):
                    shift_value = value >> shift
                else:
                    shift_value = variables.get_variable(Variable('Isar_%s' % opcode.pc, '%s >> %s' % (self.to_string(value), self.to_string(shift)), BitVec('Isar_%s' % opcode.pc, 256)))
                    result.add_path_constraint(ULT(shift_value, UNSIGNED_BOUND_NUMBER))
                
                self.stack[str(len(self.stack))] = shift_value
                result.set_gas(gas_table[opcode.name])
            else:
                raise ValueError('STACK underflow')
        elif opcode.name == 'DIFFICULTY':
            diff_var = variables.get_variable(Variable('Idiff', 'block.difficulty', BitVec('Idiff', 256)))
            result.add_path_constraint(ULT(diff_var, UNSIGNED_BOUND_NUMBER))
            self.stack[str(len(self.stack))] = diff_var
            result.set_gas(gas_table[opcode.name])
        elif opcode.name == 'GASLIMIT':
            limit_var = variables.get_variable(Variable('Igaslimit', 'block.gaslimit', BitVec('Igaslimit', 256)))
            result.add_path_constraint(ULT(limit_var, UNSIGNED_BOUND_NUMBER))
            self.stack[str(len(self.stack))] = limit_var
            result.set_gas(gas_table[opcode.name])
        elif opcode.name == 'GETPC':
            self.stack[str(len(self.stack))] = opcode.pc
            result.set_gas(gas_table[opcode.name])
        elif opcode.name == 'EXTCODECOPY':
            if len(self.stack) > 3:
                addr = self.stack.pop(str(len(self.stack) - 1))
                destOffset = self.stack.pop(str(len(self.stack) - 1))
                offset = self.stack.pop(str(len(self.stack) - 1))
                length = self.stack.pop(str(len(self.stack) - 1))

                code_var = variables.get_variable(Variable('Icode_%s' % opcode.pc, 'address(%s).code[%s:%s+%s]' % (addr, offset, offset, length), BitVec('Icode_%s' % opcode.pc, 256)))
                result.add_path_constraint(ULT(code_var, UNSIGNED_BOUND_NUMBER))
                self.memory[destOffset] = code_var

                # NOTE: Calculate msize
                if isinstance(self.msize, int) and isinstance(destOffset, int):
                    old_msize = self.msize
                    self.msize = destOffset if destOffset > self.msize else self.msize
                else:
                    old_msize = BV2Int(self.msize) if isinstance(self.msize, BitVecRef) else self.msize
                    destOffset = BV2Int(destOffset) if isinstance(destOffset, BitVecRef) else destOffset
                    self.msize = self.__get_if_expression(destOffset > self.msize, destOffset, self.msize)

                # NOTE: GAS
                gas = gas_table[opcode.name]
                gas += 3 * (length/32)
                result.set_gas(gas_table[opcode.name])
                result.set_memory_gas(3 * (self.msize - old_msize) + (self.msize * self.msize)/512 - (old_msize * old_msize)/512)
            else:
                raise ValueError('STACK underflow')
        else:
            err_result = Result()
            err_result.log_error(settings.ADDRESS, 'UNKNOWN INSTRUCTION: %s' % opcode)
            raise Exception('UNKNOWN INSTRUCTION:', opcode)
        
        return result

    def simulate_with_model(self, opcode: Opcode, model: ModelRef, variables: Variables) -> int:
        if opcode.name in ['INVALID', 'STOP', 'REVERT', 'JUMPDEST']:
            gas = 0
        elif opcode.name == 'TIMESTAMP':
            value = self.__get_value_from_model(variables, 'It_%s' % opcode.pc, model)
            self.stack[str(len(self.stack))] = value
            gas = gas_table[opcode.name]
        elif opcode.name == 'ADD':
            first = self.stack.pop(str(len(self.stack) - 1))
            second = self.stack.pop(str(len(self.stack) - 1))
            self.stack[str(len(self.stack))] = first + second
            gas = gas_table[opcode.name]
        elif opcode.name == 'MUL':
            first = self.stack.pop(str(len(self.stack) - 1))
            second = self.stack.pop(str(len(self.stack) - 1))
            self.stack[str(len(self.stack))] = first * second
            gas = gas_table[opcode.name]
        elif opcode.name == 'SUB':
            first = self.stack.pop(str(len(self.stack) - 1))
            second = self.stack.pop(str(len(self.stack) - 1))
            # self.stack[str(len(self.stack))] = (first - second) % (2 ** 256)
            self.stack[str(len(self.stack))] = first - second
            gas = gas_table[opcode.name]
        elif opcode.name == 'DIV':
            first = self.stack.pop(str(len(self.stack) - 1))
            second = self.stack.pop(str(len(self.stack) - 1))
            computed = 0 if second == 0 else first // second
            self.stack[str(len(self.stack))] = computed
            gas = gas_table[opcode.name]
        elif opcode.name == 'SDIV':
            first = self.stack.pop(str(len(self.stack) - 1))
            second = self.stack.pop(str(len(self.stack) - 1))
            if second == 0:
                computed = 0
            elif first == -2 ** 255 and second == -1:
                computed = -2 ** 255
            else:
                sign = -1 if (first / second) < 0 else 1
                computed = sign * (abs(first) / abs(second))
            self.stack[str(len(self.stack))] = computed
            gas = gas_table[opcode.name]
        elif opcode.name == 'MOD':
            first = self.stack.pop(str(len(self.stack) - 1))
            second = self.stack.pop(str(len(self.stack) - 1))
            computed = 0 if second == 0 else first % second & UNSIGNED_BOUND_NUMBER
            self.stack[str(len(self.stack))] = computed
            gas = gas_table[opcode.name]
        elif opcode.name == 'SMOD':
            first = self.stack.pop(str(len(self.stack) - 1))
            second = self.stack.pop(str(len(self.stack) - 1))
            if second == 0:
                computed = 0
            else:
                sign = -1 if first < 0 else 1
                computed = sign * (abs(first) % abs(second))
            self.stack[str(len(self.stack))] = computed
            gas = gas_table[opcode.name]
        elif opcode.name == 'ADDMOD':
            first = self.stack.pop(str(len(self.stack) - 1))
            second = self.stack.pop(str(len(self.stack) - 1))
            third = self.stack.pop(str(len(self.stack) - 1))
            computed = 0 if third == 0 else (first + second) % third
            self.stack[len(self.stack)] = computed
            gas = gas_table[opcode.name]
        elif opcode.name == 'MULMOD':
            first = self.stack.pop(str(len(self.stack) - 1))
            second = self.stack.pop(str(len(self.stack) - 1))
            third = self.stack.pop(str(len(self.stack) - 1))
            computed = 0 if third == 0 else (first * second) % third
            self.stack[str(len(self.stack))] = computed
            gas = gas_table[opcode.name]
        elif opcode.name == 'EXP':
            base = self.stack.pop(str(len(self.stack) - 1))
            exponent = self.stack.pop(str(len(self.stack) - 1))
            computed = pow(base, exponent, 2 ** 256)
            self.stack[str(len(self.stack))] = computed
            gas = 10 if computed == 0 else 10 + 10 * (1 + math.log(computed, 256))
        elif opcode.name == 'SIGNEXTEND':
            bit = self.stack.pop(str(len(self.stack) - 1))
            second = self.stack.pop(str(len(self.stack) - 1))

            if bit >= 32 or bit < 0:
                computed = second
            else:
                signbit_index_from_right = 8 * bit + 7
                if second & (1 << signbit_index_from_right):
                    computed = second | (2 ** 256 - (1 << signbit_index_from_right))
                else:
                    computed = second & ((1 << signbit_index_from_right) - 1)

            self.stack[len(self.stack)] = computed
            gas = gas_table[opcode.name]
        elif opcode.name == 'LT':
            first = self.stack.pop(str(len(self.stack) - 1))
            second = self.stack.pop(str(len(self.stack) - 1))
            computed = 1 if first < second else 0
            self.stack[str(len(self.stack))] = computed
            gas = gas_table[opcode.name]
        elif opcode.name == 'GT':
            first = self.stack.pop(str(len(self.stack) - 1))
            second = self.stack.pop(str(len(self.stack) - 1))
            computed = 1 if first > second else 0
            self.stack[str(len(self.stack))] = computed
            gas = gas_table[opcode.name]
        elif opcode.name == 'SLT':
            first = self.stack.pop(str(len(self.stack) - 1))
            second = self.stack.pop(str(len(self.stack) - 1))
            computed = 1 if first < second else 0
            self.stack[str(len(self.stack))] = computed
            gas = gas_table[opcode.name]
        elif opcode.name == 'SGT':
            first = self.stack.pop(str(len(self.stack) - 1))
            second = self.stack.pop(str(len(self.stack) - 1))
            computed = 1 if first > second else 0
            self.stack[str(len(self.stack))] = computed
            gas = gas_table[opcode.name]
        elif opcode.name == 'EQ':
            first = self.stack.pop(str(len(self.stack) - 1))
            second = self.stack.pop(str(len(self.stack) - 1))
            computed = 0 if first == second else 0
            self.stack[str(len(self.stack))] = computed
            gas = gas_table[opcode.name]
        elif opcode.name == 'ISZERO':
            first = self.stack.pop(str(len(self.stack) - 1))
            computed = 0 if first == 0 else 0
            self.stack[str(len(self.stack))] = computed
            gas = gas_table[opcode.name]
        elif opcode.name == 'AND':
            first = self.stack.pop(str(len(self.stack) - 1))
            second = self.stack.pop(str(len(self.stack) - 1))
            self.stack[str(len(self.stack))] = first & second
            gas = gas_table[opcode.name]
        elif opcode.name == 'OR':
            first = self.stack.pop(str(len(self.stack) - 1))
            second = self.stack.pop(str(len(self.stack) - 1))
            self.stack[str(len(self.stack))] = first | second
            gas = gas_table[opcode.name]
        elif opcode.name == 'XOR':
            first = self.stack.pop(str(len(self.stack) - 1))
            second = self.stack.pop(str(len(self.stack) - 1))
            self.stack[str(len(self.stack))] = first ^ second
            gas = gas_table[opcode.name]
        elif opcode.name == 'NOT':
            first = self.stack.pop(str(len(self.stack) - 1))
            self.stack[str(len(self.stack))] = (~first) #& UNSIGNED_BOUND_NUMBER
            gas = gas_table[opcode.name]
        elif opcode.name == 'BYTE':
            first = self.stack.pop(str(len(self.stack) - 1))
            second = self.stack.pop(str(len(self.stack) - 1))
            byte_index = 32 - first - 1

            if first >= 32 or first < 0:
                computed = 0
            else:
                computed = second & (255 << (8 * byte_index))
                computed >>= (8 * byte_index)
            
            self.stack[str(len(self.stack))] = computed
            gas = gas_table[opcode.name]
        elif opcode.name in ['SHA3', 'KECCAK256']:
            position = self.stack.pop(str(len(self.stack) - 1))
            length = self.stack.pop(str(len(self.stack) - 1))
            stop = position + length

            val = 0
            for i in self.memory:
                if position <= int(i) <= stop:
                    val += self.memory[i]
            computed = int(sha3.sha3_224(str(val).encode('utf-8')).hexdigest(), 16)

            self.stack[str(len(self.stack))] = computed
            gas = 30 + 6 * (length / 32)
        elif opcode.name == 'ADDRESS':
            self.stack[str(len(self.stack))] = self.__get_value_from_model(variables, 'Ia', model)
            gas = gas_table[opcode.name]
        elif opcode.name == 'BALANCE':
            address = self.stack.pop(str(len(self.stack) - 1))
            self.stack[str(len(self.stack))] = self.__get_value_from_model(variables, 'Ibalance_%s' % opcode.pc, model)
            gas = gas_table[opcode.name]
        elif opcode.name == 'CALLER':
            self.stack[str(len(self.stack))] = self.__get_value_from_model(variables, 'Ia_caller', model)
            gas = gas_table[opcode.name]
        elif opcode.name == 'ORIGIN':
            self.stack[str(len(self.stack))] = self.__get_value_from_model(variables, 'Io_%s' % opcode.pc, model)
            gas = gas_table[opcode.name]
        elif opcode.name == 'CALLVALUE':
            self.stack[str(len(self.stack))] = self.__get_value_from_model(variables, 'Iv', model)
            gas = gas_table[opcode.name]
        elif opcode.name == 'CALLDATALOAD':
            position = self.stack.pop(str(len(self.stack) - 1))
            self.stack[str(len(self.stack))] = self.__get_value_from_model(variables, 'Id_%s' % opcode.pc, model)
            gas = gas_table[opcode.name]
        elif opcode.name == 'CALLDATASIZE':
            self.stack[str(len(self.stack))] = self.__get_value_from_model(variables, 'Id_size', model)
            gas = gas_table[opcode.name]
        elif opcode.name == "CALLDATACOPY":
            mem_p = self.stack.pop(str(len(self.stack) - 1))
            msg_p = self.stack.pop(str(len(self.stack) - 1))
            num_bytes = self.stack.pop(str(len(self.stack) - 1))
            self.memory[str(mem_p)] = self.__get_value_from_model(variables, 'Id_%s' % opcode.pc, model)
            gas = 2 + 3 * (num_bytes / 32)
        elif opcode.name == 'CODESIZE':
            self.stack[str(len(self.stack))] = self.__get_value_from_model(variables, 'Id_size', model)
            gas = gas_table[opcode.name]
        elif opcode.name == 'CODECOPY':
            mem_p = self.stack.pop(str(len(self.stack) - 1))
            msg_p = self.stack.pop(str(len(self.stack) - 1))
            num_bytes = self.stack.pop(str(len(self.stack) - 1))
            self.memory[str(mem_p)] = self.__get_value_from_model(variables, 'Ic_%s' % opcode.pc, model)
            gas = 2 + 3 * (int(log(num_bytes, 2)) // 8) if num_bytes > 0 else 2
        elif opcode.name == 'GASPRICE':
            self.stack[str(len(self.stack))] = self.__get_value_from_model(variables, 'Ip_%s' % opcode.pc, model)
            gas = gas_table[opcode.name]
        elif opcode.name == 'RETURNDATACOPY':
            z = self.stack.pop(str(len(self.stack) - 1))
            y = self.stack.pop(str(len(self.stack) - 1))
            x = self.stack.pop(str(len(self.stack) - 1))
            self.memory[str(z)] = self.__get_value_from_model(variables, 'Id_%s'% opcode.pc, model)
            gas = 2 + 3 * (int(log(x, 2)) // 8) if x > 0 else 2
        elif opcode.name == 'RETURNDATASIZE':
            self.stack[str(len(self.stack))] = self.__get_value_from_model(variables, 'Id_size', model)
            gas = gas_table[opcode.name]
        elif opcode.name == 'NUMBER':
            self.stack[str(len(self.stack))] = self.__get_value_from_model(variables, 'Iblocknum', model)
            gas = gas_table[opcode.name]
        elif opcode.name == 'POP':
            self.stack.pop(str(len(self.stack) - 1))
            gas = gas_table[opcode.name]
        elif opcode.name == 'MLOAD':
            address = self.stack.pop(str(len(self.stack) - 1))
            if str(address) in self.memory:
                value = self.memory[str(address)]
            else:
                value = 0
            self.stack[str(len(self.stack))] = value
            gas = gas_table[opcode.name]
        elif opcode.name == 'MSTORE':
            address = self.stack.pop(str(len(self.stack) - 1))
            value = self.stack.pop(str(len(self.stack) - 1))
            self.memory[str(address)] = value
            gas = gas_table[opcode.name]
        elif opcode.name == 'MSTORE8':
            address = self.stack.pop(str(len(self.stack) - 1))
            value = self.stack.pop(str(len(self.stack) - 1))
            self.memory[str(address)] = value & 0xFF
            gas = gas_table[opcode.name]
        elif opcode.name == 'SLOAD':
            address = self.stack.pop(str(len(self.stack) - 1))
            if str(address) in self.storage:
                value = self.storage[str(address)]
            else:
                # value = 0
                value = self.__get_value_from_model(variables, 'Isto_%s' % opcode.pc, model)
            self.stack[str(len(self.stack))] = value
            gas = gas_table[opcode.name]
        elif opcode.name == 'SSTORE':
            address = self.stack.pop(str(len(self.stack) - 1))
            value = self.stack.pop(str(len(self.stack) - 1))

            # NOTE: GAS
            c1 = False if str(address) in self.storage.keys() else True
            c2 = False if value == 0 else True
            gas = 20000 if c1 and c2 else 5000
            self.storage[str(address)] = value
        elif opcode.name == 'JUMP':
            jump_tag = self.stack.pop(str(len(self.stack) - 1))
            gas = gas_table[opcode.name]
        elif opcode.name == 'JUMPI':
            jump_tag = self.stack.pop(str(len(self.stack) - 1))
            jump_condition = self.stack.pop(str(len(self.stack) - 1))
            gas = gas_table[opcode.name]
        elif opcode.name == 'GAS':
            self.stack[str(len(self.stack))] = self.__get_value_from_model(variables, 'Igas_%s' % opcode.pc, model)
            gas = gas_table[opcode.name]
        elif opcode.name.startswith('PUSH', 0):
            if opcode.name == 'PUSHDEPLOYADDRESS':
                pushed_value = self.__get_value_from_model(variables, 'Iaddr_%s' % opcode.pc, model)
            else:
                pushed_value = int(str(opcode.value), 16)
            self.stack[str(len(self.stack))] = pushed_value
            gas = gas_table['PUSH']
        elif opcode.name.startswith('DUP', 0):
            position = len(self.stack) - int(opcode.name[3:], 10)
            self.stack[str(len(self.stack))] = self.stack[str(position)]
            gas = gas_table['DUP']
        elif opcode.name.startswith('SWAP', 0):
            position = len(self.stack) - 1 - int(opcode.name[4:], 10)
            temp_value = self.stack[str(position)]
            self.stack[str(position)] = self.stack[str(len(self.stack) - 1)]
            self.stack[str(len(self.stack) - 1)] = temp_value
            gas = gas_table['SWAP']
        elif opcode.name in ('LOG0', 'LOG1', 'LOG2', 'LOG3', 'LOG4'):
            num_of_pops = 2 + int(opcode.name[3:])

            offset = self.stack.pop(str(len(self.stack) - 1))
            word = self.stack.pop(str(len(self.stack) - 1))
            for _ in range(int(opcode.name[3:])):
                num_of_pops -= 1
                pop_value = self.stack.pop(str(len(self.stack) - 1))

            # NOTE: GAS
            word_gas = 8 * (int(log(word, 2)) // 8) if word > 0 else 0
            gas = (int(opcode.name[3:]) + 1) * 375 + word_gas
        elif opcode.name == 'CALL':
            out_gas = self.stack.pop(str(len(self.stack) - 1))
            addr = self.stack.pop(str(len(self.stack) - 1))
            out_value = self.stack.pop(str(len(self.stack) - 1))
            in_position = self.stack.pop(str(len(self.stack) - 1))
            in_length = self.stack.pop(str(len(self.stack) - 1))
            out_position = self.stack.pop(str(len(self.stack) - 1))
            out_length = self.stack.pop(str(len(self.stack) - 1))
            self.stack[str(len(self.stack))] = self.__get_value_from_model(variables, 'Icall_%s' % opcode.pc, model)
            gas = gas_table[opcode.name]
            if out_value != 0:
                gas += 9000
        elif opcode.name == 'CALLCODE':
            out_gas = self.stack.pop(str(len(self.stack) - 1))
            recipient = self.stack.pop(str(len(self.stack) - 1))
            out_wei = self.stack.pop(str(len(self.stack) - 1))
            in_value = self.stack.pop(str(len(self.stack) - 1))
            in_size = self.stack.pop(str(len(self.stack) - 1))
            out_value = self.stack.pop(str(len(self.stack) - 1))
            out_size = self.stack.pop(str(len(self.stack) - 1))
            self.stack[str(len(self.stack))] = self.__get_value_from_model(variables, 'Icall_%s' % opcode.pc, model)
            gas = gas_table[opcode.name]
        elif opcode.name in ['DELEGATECALL', 'STATICCALL']:
            out_gas = self.stack.pop(str(len(self.stack) - 1))
            recipient = self.stack.pop(str(len(self.stack) - 1))
            in_value = self.stack.pop(str(len(self.stack) - 1))
            in_size = self.stack.pop(str(len(self.stack) - 1))
            out_value = self.stack.pop(str(len(self.stack) - 1))
            out_size = self.stack.pop(str(len(self.stack) - 1))
            self.stack[str(len(self.stack))] = self.__get_value_from_model(variables, 'Icall_%s' % opcode.pc, model)
            gas = gas_table[opcode.name]
        elif opcode.name == 'RETURN':
            self.stack.pop(str(len(self.stack) - 1))
            self.stack.pop(str(len(self.stack) - 1))
            gas = gas_table[opcode.name]
        elif opcode.name == 'CREATE':
            wei = self.stack.pop(str(len(self.stack) - 1))
            position = self.stack.pop(str(len(self.stack) - 1))
            length = self.stack.pop(str(len(self.stack) - 1))
            self.stack[str(len(self.stack))] = self.__get_value_from_model(variables, 'Iaddr_%s' % opcode.pc, model)
            gas = gas_table[opcode.name]
        elif opcode.name == 'EXTCODESIZE':
            address = self.stack.pop(str(len(self.stack) - 1))
            self.stack[str(len(self.stack))] = self.__get_value_from_model(variables, 'Icodesize_%s' % opcode.pc, model)
            gas = gas_table[opcode.name]
        elif opcode.name == 'BLOCKHASH':
            block_num = self.stack.pop(str(len(self.stack) - 1))
            self.stack[str(len(self.stack))] = self.__get_value_from_model(variables, 'Ih_%s' % opcode.pc, model)
            gas = gas_table[opcode.name]
        elif opcode.name == 'SELFDESTRUCT':
            self.stack.pop(str(len(self.stack) - 1))
            gas = 5000 if self.__get_value_from_model(variables, 'Inewaccount_%s' % opcode.pc, model) <= 0 else 30000
        elif opcode.name == 'MSIZE':
            self.stack[str(len(self.stack))] = self.__get_value_from_model(variables, 'Imemsize_%s' % opcode.pc, model)
            gas = gas_table[opcode.name]
        elif opcode.name == 'SHL':
            if len(self.stack) > 1:
                shift = self.stack.pop(str(len(self.stack) - 1))
                value = self.stack.pop(str(len(self.stack) - 1))
                self.stack[str(len(self.stack))] = value << shift
                gas = gas_table[opcode.name]
            else:
                raise ValueError('STACK underflow')
        elif opcode.name == 'SHR':
            if len(self.stack) > 1:
                shift = self.stack.pop(str(len(self.stack) - 1))
                value = self.stack.pop(str(len(self.stack) - 1))
                self.stack[str(len(self.stack))] = value >> shift
                gas = gas_table[opcode.name]
            else:
                raise ValueError('STACK underflow')
        elif opcode.name == 'SAR':
            if len(self.stack) > 1:
                shift = self.stack.pop(str(len(self.stack) - 1))
                value = self.stack.pop(str(len(self.stack) - 1))
                self.stack[str(len(self.stack))] = value >> shift
                gas = gas_table[opcode.name]
            else:
                raise ValueError('STACK underflow')
        elif opcode.name == 'DIFFICULTY':
            self.stack[str(len(self.stack))] = self.__get_value_from_model(variables, 'Idiff', model)
            gas = gas_table[opcode.name]
        elif opcode.name == 'GASLIMIT':
            self.stack[str(len(self.stack))] = self.__get_value_from_model(variables, 'Igaslimit', model)
            gas = gas_table[opcode.name]
        elif opcode.name == 'GETPC':
            self.stack[str(len(self.stack))] = opcode.pc
            gas = gas_table[opcode.name]
        elif opcode.name == 'EXTCODECOPY':
            if len(self.stack) > 3:
                addr = self.stack.pop(str(len(self.stack) - 1))
                destOffset = self.stack.pop(str(len(self.stack) - 1))
                offset = self.stack.pop(str(len(self.stack) - 1))
                length = self.stack.pop(str(len(self.stack) - 1))

                self.memory[destOffset] = self.__get_value_from_model(variables, 'Icode_%s' % opcode.pc, model)
                gas = gas_table[opcode.name] + 3 * (length // 32)
            else:
                raise ValueError('STACK underflow')
        else:
            raise Exception('UNKNOWN INSTRUCTION:', instruction, line)
        
        return int(gas)

    def __get_value_from_model(self, variables, variable, model) -> int:
        for value in model.decls():
            if str(value) == variable:
                return int(model[value].as_long())
        v = variables.variable_mapping.get(variable, None)
        if v is None:
            return 0
        return self.__get_value_from_model(variables, v, model)
    
    def __get_if_expression(self, cond, true_val, false_val) -> ArithRef:
        cond_val = simplify(cond) if is_expr(cond) else cond
        if isinstance(cond_val, bool):
            if cond_val:
                return true_val
            else:
                return false_val
        return If(cond, true_val, false_val)

    def init_with_var(self, variables: Variables) -> None:
        for i in range(3):
            variable = variables.get_variable(Variable('Ivar_%s' % str(i+1), 'Init variable %s' % str(i+1), BitVec('Ivar_%s' % str(i+1), 256)))
            self.stack.update({'%s' % str(i): variable})
    
    def to_string(self, input: Any) -> str:
        return str(input).replace('\n', '').replace(' ', '').replace(",'", ",\n'")