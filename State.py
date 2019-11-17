import sha3
from z3_func import *
from gas_price import gas_table
from settings import *
from Opcode import Opcode
from SimulationResult import SimularionResult
from PathConstraint import PathConstraint
from Variable import Variable

class State:

    def __init__(self):
        self.stack = dict()
        self.memory = dict()
        self.storage = dict()
        self.solver = Solver()

    def simulate(self, opcode: Opcode) -> SimularionResult:
        variables = VARIABLES
        result = SimularionResult()

        if opcode.name in ['INVALID', 'STOP', 'REVERT', 'JUMPDEST']:
            pass
        elif opcode.name == 'TIMESTAMP':
            time_var = BitVec('It_%s' % opcode.pc, 256)
            variables.add_variable(Variable('It_%s' % opcode.pc, 'TIMESTAMP', time_var))
            result.add_path_constraint(PathConstraint(ULT(time_var, UNSIGNED_BOUND_NUMBER)))

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
                    computed = (first + second) % (2 ** 256)

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
                computed = first * second & UNSIGNED_BOUND_NUMBER
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
                    computed = (first - second) % (2 ** 256)
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
                    if second == 0:
                        computed = 0
                    else:
                        first = to_unsigned(first)
                        second = to_unsigned(second)
                        computed = first // second
                else:
                    if is_real(second):
                        computed = first / second
                    else:
                        computed = If(second == 0, 0, first/second)
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
                            z3_abs = lambda x: If(x >= 0, x, -x)
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
                        computed = first % second & UNSIGNED_BOUND_NUMBER

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

                        z3_abs = lambda x: If(x >= 0, x, -x)
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
                    computed = BitVec('Iexp_%s' % opcode.pc, 256)
                    variables.add_variable(Variable('Iexp_%s', 'EXP(%s, %s)' % (base, exponent), computed))
                    result.add_path_constraint(ULT(computed, UNSIGNED_BOUND_NUMBER))

                    # NOTE: GAS
                    if is_real(computed):
                        gas = 10 + 10 * (1 + math.log(computed, 256))
                    else:
                        if isinstance(base, int) and base == 256:
                            gas = simplify(10 + (10 * (1 + BV2Int(exponent)))) if is_bv(exponent) else simplify(10 + (10 * (1 + exponent)))
                        else:
                            gas_var = BitVec('log_%s' % opcode.pc, 256)
                            gas = simplify(10 + (10 * (1 + BV2Int(gas_var))))
                            result.add_path_constraint(ULT(gas_var, UNSIGNED_BOUND_NUMBER))
                            variables.add_variable(Variable('log_%s' % opcode.pc, 'log256(%s)' % computed, gas_var))

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
                        computed = If(ULT(first, second), BitVecVal(1, 256), BitVecVal(0, 256))
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
                    computed = If(UGT(first, second), BitVecVal(1, 256), BitVecVal(0, 256))
                # computed = simplify(computed) if is_expr(computed) else computed

                self.stack[str(len(self.stack))] = computed
                result.set_gas(gas_table[opcode.name])
            else:
                raise ValueError('STACK underflow')
        elif opcode.name == 'SLT':
            if len(self.stack) > 1:
                first = self.stack.pop(len(self.stack) - 1)
                second = self.stack.pop(len(self.stack) - 1)

                if is_all_real(first, second):
                    first = to_signed(first)
                    second = to_signed(second)
                    computed = 1 if first < second else 0
                else:
                    computed = If(first < second, BitVecVal(1, 256), BitVecVal(0, 256))
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
                    computed = If(first > second, BitVecVal(1, 256), BitVecVal(0, 256))
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
                    computed = If(first == second, BitVecVal(1, 256), BitVecVal(0, 256))
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
                    computed = If(first.arg(0), first.arg(2), first.arg(1)) if condiiton else If(first == 0, BitVecVal(1, 256), BitVecVal(0, 256))
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
                                data = simplify(data) if is_expr(data) else data
                        else:
                            mem_var = BitVec('Imem_%s' % opcode.pc, 256)
                            data = data + mem_var
                            result.add_path_constraint(ULT(mem_var, UNSIGNED_BOUND_NUMBER))
                            result.add_path_constraint(ULT(data, UNSIGNED_BOUND_NUMBER))
                            variables.add_variable(Variable('Imem_%s' % opcode.pc, 'memory[%s:%s+32]' % (i, i), mem_var))
                else:
                    data = BitVec('Isha3_%s' % opcode.pc, 256)
                    result.add_path_constraint(ULT(data, UNSIGNED_BOUND_NUMBER))
                    variables.add_variable(Variable('Isha3_%s' % opcode.pc, 'SHA3(memory[%s:%s])' % (position, position + length), data))

                if isinstance(data, int):
                    computed = int(sha3.sha3_224(str(data).encode('utf-8')).hexdigest(), 16)
                else:
                    computed = variables.get_z3_var_by_value('SHA3(%s)' % data)
                    if computed is None:
                        computed = BitVec('Isha3_%s' % opcode.pc, 256)
                        result.add_path_constraint(ULT(computed, UNSIGNED_BOUND_NUMBER))
                        variables.add_variable(Variable('Isha3_%s' % opcode.pc, 'SHA3(%s)' % data, computed))
                # data = simplify(data) if is_expr(data) else data

                self.stack[str(len(self.stack))] = computed

                # NOTE: GAS
                if isinstance(length, int):
                    gas = 30 + 6 * (length/32)
                else:
                    if str(data) == 'Ia_caller':
                        gas = 150
                    else:
                        size_var = BitVec('Isize_%s' % opcode.pc, 256)
                        result.add_path_constraint(ULT(size_var, BYTE_BOUND_NUMBER))
                        variables.add_variable(Variable('Isize_%s' % opcode.pc, 'The word size of %s' % data, size_var))
                        gas = simplify(30 + 6 * BV2Int(size_var))

                result.set_gas(gas)
            else:
                raise ValueError('STACK underflow')
        elif opcode.name == 'ADDRESS':
            addr_var = BitVec('Ia', 256)
            result.add_path_constraint(ULT(addr_var, UNSIGNED_BOUND_NUMBER))
            variables.add_variable(Variable('Ia', 'address(this) (address of the executing contract)', addr_var))

            self.stack[str(len(self.stack))] = addr_var
            result.set_gas(gas_table[opcode.name])
        elif opcode.name == 'BALANCE':
            if len(self.stack) > 0:
                address = self.stack.pop(str(len(self.stack) - 1))

                banlance_var = BitVec('balance_%s' % opcode.pc, 256)
                result.add_path_constraint(ULT(banlance_var, UNSIGNED_BOUND_NUMBER))
                variables.add_variable(Variable('balance_%s' % opcode.pc, 'address(%s).balance' % address, banlance_var))

                self.stack[str(len(self.stack))] = banlance_var
                result.set_gas(gas_table[opcode.name])
            else:
                raise ValueError('STACK underflow')
        elif opcode.name == 'CALLER':
            caller_var = BitVec('Ia_caller', 256)
            result.add_path_constraint(ULT(caller_var, UNSIGNED_BOUND_NUMBER))
            variables.add_variable(Variable('Ia_caller', 'msg.caller (caller address)', caller_var))

            self.stack[str(len(self.stack))] = caller_var
            result.set_gas(gas_table[opcode.name])
        elif opcode.name == "ORIGIN":
            origin_var = BitVec('Io_%s' % opcode.pc, 256)
            result.add_path_constraint(ULT(origin_var, UNSIGNED_BOUND_NUMBER))
            variables.add_variable(Variable('Io_%s' % opcode.pc, 'tx.origin (transaction origin address)', origin_var))

            self.stack[str(len(self.stack))] = caller_var
            result.set_gas(gas_table[opcode.name])
        elif opcode.name == 'CALLVALUE':
            value_var = BitVec('Iv', 256)
            result.add_path_constraint(ULT(value_var, UNSIGNED_BOUND_NUMBER))
            variables.add_variable(Variable('Iv', 'tx.origin (transaction origin address)', value_var))

            self.stack[str(len(self.stack))] = value_var
            result.set_gas(gas_table[opcode.name])
        elif opcode.name == 'CALLDATALOAD':
            if len(self.stack) > 0:
                position = self.stack.pop(str(len(self.stack) - 1))

                # NOTE: Check if the sym var of msg.data is already created or not
                if isinstance(position, int):
                    data_var = variables.get_z3_var_by_value('msg.data[%s:%s]' % (position, position + 32))
                else:
                    data_var = variables.get_z3_var_by_value('msg.data[%s:%s]' % (position, simplify(position+32)))
                if data_var is None:
                    data_var = BitVec('Id_%s' % opcode.pc, 256)
                    result.add_path_constraint(ULT(data_var, UNSIGNED_BOUND_NUMBER))
                    if isinstance(position, int):
                        variables.add_variable(Variable('Id_%s' % opcode.pc, 'msg.data[%s:%s]' % (position, position + 32), data_var))
                    else:
                        pass
                        # variables.add_variable(Variable('Id_%s' % opcode.pc, 'msg.data[%s:%s]' % (position, simplify(position+32), data_var))

                self.stack[str(len(self.stack))] = data_var
                result.set_gas(gas_table[opcode.name])
            else:
                raise ValueError('STACK underflow')
        elif opcode.name == 'CALLDATASIZE':
            ds_var = BitVec('Id_size', 256)
            variables.add_variable(Variable('Id_size', 'msg.data.size', ds_var))

            self.stack[str(len(self.stack))] = ds_var
            result.set_gas(gas_table[opcode.name])
        elif opcode.name == "CALLDATACOPY":
            if len(self.stack) > 2:
                mem_p = self.stack.pop(str(len(self.stack) - 1))
                msg_p = self.stack.pop(str(len(self.stack) - 1))
                num_bytes = self.stack.pop(str(len(self.stack) - 1))

                data_var = BitVec('Id_%s' % opcode.pc, 256)
                result.add_path_constraint(ULT(data_var, UNSIGNED_BOUND_NUMBER))
                variables.add_variable(Variable('Id_%s' % opcode.pc, 'msg.data[%s:%s+%s]' % (msg_p, msg_p, num_bytes), data_var))
                self.memory[mem_p] = data_var

                # NOTE: GAS
                if is_real(num_bytes):
                    gas = 2 + 3 * (len(hex(num_bytes))-2)
                else:
                    ws_var = BitVec('Isize_%s' % opcode.pc, 256)
                    result.add_path_constraint(ULT(ws_var, BYTE_BOUND_NUMBER))
                    variables.add_variable(Variable('Isize_%s' % opcode.pc, 'The word size of %s' % num_bytes, ws_var))
                    gas = simplify(2 + 3 * BV2Int(ws_var))
                result.set_gas(gas)
            else:
                raise ValueError('STACK underflow')
        elif opcode.name == 'CODESIZE':
            size_var = BitVec('Id_size', 256)
            result.add_path_constraint(ULT(size_var, UNSIGNED_BOUND_NUMBER))
            variables.add_variable(Variable('Id_size', 'address(this).code.size', size_var))

            self.stack[str(len(self.stack))] = size_var
            result.set_gas(gas_table[opcode.name])
        elif opcode.name == 'CODECOPY':
            if len(self.stack) > 2:
                mem_p = self.stack.pop(str(len(self.stack) - 1))
                msg_p = self.stack.pop(str(len(self.stack) - 1))
                num_bytes = self.stack.pop(str(len(self.stack) - 1))

                code_var = BitVec('Ic_%s' % opcode.pc, 256)
                result.add_path_constraint(ULT(code_var, UNSIGNED_BOUND_NUMBER))
                variables.add_variable(Variable('Ic_%s' % opcode.pc, 'address(this).code[%s:%s+%s]' % (mem_p, msg_p, num_bytes), code_var))
                self.memory[mem_p] = code_var

                # NOTE: GAS
                if is_real(num_bytes):
                    gas = 2 + 3 * (len(hex(num_bytes)) - 2)
                else:
                    size_var = BitVec('Isize_%s' % str(num_bytes).split('_')[1], 256)
                    result.add_path_constraint(ULT(size_var, BYTE_BOUND_NUMBER))
                    variables.add_variable(Variable('Isize_%s' % str(num_bytes).split('_')[1], 'The word size of %s' % num_bytes, size_var))

                    gas = simplify(30 + 6 * BV2Int(size_var))
                result.set_gas(gas)
            else:
                raise ValueError('STACK underflow')
        elif opcode.name == 'GASPRICE':
            gas_var = BitVec('Ip_%s' % opcode.pc, 256)
            result.add_path_constraint(ULT(gas_var, UNSIGNED_BOUND_NUMBER))
            variables.add_variable(Variable('Ip_%s' % opcode.pc, 'tx.gasprice', gas_var))

            self.stack[str(len(self.stack))] = gas_var
            result.set_gas(gas_table[opcode.name])
        elif opcode.name == 'RETURNDATACOPY':
            if len(self.stack) > 2:
                z = self.stack.pop(str(len(self.stack) - 1))
                y = self.stack.pop(str(len(self.stack) - 1))
                x = self.stack.pop(str(len(self.stack) - 1))

                data_var = variables.get_z3_var_by_value('RETURNDATA[%s:%s+%s]' % (y, y, x))
                if data_var is None:
                    data_var = BitVec('Id_%s'% opcode.pc, 256)
                    result.add_path_constraint(ULT(data_var, UNSIGNED_BOUND_NUMBER))
                    variables.add_variable(Variable('Id_%s'% opcode.pc, 'RETURNDATA[%s:%s+%s]' % (y, y, x), data_var))
                self.memory[z] = data_var

                # NOTE: GAS
                if is_real(x):
                    gas = 2 + 3 * (len(hex(x)) - 2)
                else:
                    size_var = BitVec('Isize_%s' % str(x).split('_')[1], 256)
                    result.add_path_constraint(ULT(size_var, BYTE_BOUND_NUMBER))
                    variables.add_variable(Variable('Isize_%s' % str(x).split('_')[1], 'The word size of %s' % x, size_var))
                    gas = simplify(30 + 6 * BV2Int(size_var))
                result.set_gas(gas)
            else:
                raise ValueError('STACK underflow')
        elif opcode.name == 'RETURNDATASIZE':
            size_var = BitVec('Id_size', 256)
            result.add_path_constraint(ULT(size_var, BYTE_BOUND_NUMBER))
            variables.add_variable(Variable('Id_size', 'data.size', size_var))

            self.stack[str(len(self.stack))] = size_var
            result.set_gas(gas_table[opcode.name])
        elif opcode.name == 'NUMBER':
            number_var = BitVec('Iblocknum', 256)
            result.add_path_constraint(ULT(number_var, BYTE_BOUND_NUMBER))
            variables.add_variable(Variable('Iblocknum', 'block.number', number_var))

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
                    value = If(self.memory == list(self.memory.keys())[0], self.memory[list(self.memory.keys())[0]], BitVecVal(0, 256))
                    if len(self.memory) > 1:
                        tem_val = value
                        for key, val in self.memory.items():
                            value = If(address == key, val, tem_val)
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
                self.memory[address] = value
                result.set_gas(gas_table[opcode.name])
            else:
                raise ValueError('STACK underflow')
        elif opcode.name == 'SLOAD':
            if len(self.stack) > 0:
                address = self.stack.pop(str(len(self.stack) - 1))

                if len(self.storage) == 0:
                    value = 0
                else:
                    value = self.storage.get(str(address), None)

                    if value is None:
                        value = If(address == list(self.storage.keys())[0], self.storage[list(self.storage.keys())[0]], BitVecVal(0, 256))
                        if len(self.storage) > 1:
                            tem_val = value
                            for key, val in self.storage.items():
                                cond = address == key
                                if cond == True:
                                    value = val
                                    tem_val = value
                                elif cond == False:
                                    continue
                                else:
                                    value = If(address == key, val, tem_val)
                                    tem_val = value
                        value_s = simplify(value) if is_expr(value) else value
                        value = value_s.as_long() if isinstance(value_s, BitVecNumRef) else value

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
                        gas = simplify(BV2Int(If(Not(value == 0), BitVecVal(20000, 256), BitVecVal(5000, 256))))
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
                            gas = simplify(BV2Int(If(Or(value == 0, cond), BitVecVal(5000, 256), BitVecVal(20000, 256))))
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
            gas_var = BitVec('Igas_%s' % opcode.pc, 256)
            result.add_path_constraint(ULT(gas_var, UNSIGNED_BOUND_NUMBER))
            variables.add_variable(Variable('Igas_%s' % opcode.pc, 'Gas Remaining', gas_var))

            self.stack[str(len(self.stack))] = gas_var
            result.set_gas(gas_table[opcode.name])
        elif opcode.name.startswith('PUSH', 0):
            if opcode.name == 'PUSHDEPLOYADDRESS':
                pushed_value = BitVec('Iaddr_%s' % opcode.pc, 256)
                result.add_path_constraint(ULT(pushed_value, UNSIGNED_BOUND_NUMBER))
                variables.add_variable(Variable('Iaddr_%s' % opcode.pc, 'address(deployed)', pushed_value))
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
            if len(self.stack) > position:
                temp_value = self.stack[str(position)]
                self.stack[str(position)] = self.stack[str(len(self.stack) - 1)]
                self.stack[str(len(self.stack) - 1)] = temp_value
                result.set_gas(gas_table['SWAP'])
            else:
                raise ValueError('STACK underflow')
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
                    gas = (int(opcode.name[3:]) + 1) * 375 + (8 * (len(hex(word)) - 2))
                else:
                    size_var = BitVec('Isize_%s' % opcode.pc, 256)
                    result.add_path_constraint(ULT(size_var, BYTE_BOUND_NUMBER))
                    variables.add_variable(Variable('Isize_%s' % opcode.pc, 'The bytes of %s' % word, size_var))
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

                call_var = BitVec('Icall_%s' % opcode.pc, 256)
                result.add_path_constraint(Or(call_var == 1, call_var == 0))
                variables.add_variable(Variable('Icall_%s' % opcode.pc, 'call success or not', call_var))
                self.stack[str(len(self.stack))] = call_var

                # NOTE: GAS
                # FIXME: fix gas
                gas = gas_table[opcode.name]
                out_value = out_value.as_long() if isinstance(out_value, z3.z3.BitVecNumRef) else out_value
                if isinstance(out_value, int) and out_value != 0:
                    gas += 9000
                elif is_expr(out_value):
                    g = If(out_value == 0, 0, 9000)
                    if is_bv(g):
                        gas += BV2Int(If(out_value == 0, 0, 9000))
                    else:
                        gas += If(out_value == 0, 0, 9000)
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

                call_var = BitVec('Icall_%s' % opcode.pc, 256)
                result.add_path_constraint(Or(call_var == 1, call_var == 0))
                variables.add_variable(Variable('Icall_%s' % opcode.pc, 'call success or not', call_var))
                self.stack[str(len(self.stack))] = call_var
                # FIXME: fix gas
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

                call_var = BitVec('Icall_%s' % opcode.pc, 256)
                result.add_path_constraint(Or(call_var == 1, call_var == 0))
                variables.add_variable(Variable('Icall_%s' % opcode.pc, 'call success or not', call_var))
                self.stack[str(len(self.stack))] = call_var
                # FIXME: fix gas
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

                addr_var = BitVec('Iaddr_%s' % opcode.pc, 256)
                result.add_path_constraint(ULT(addr_var, ADDRESS_BOUND_NUMBER))
                variables.add_variable(Variable('Iaddr_%s' % opcode.pc, 'memory[%s:%s].value(%s)' % (offset, offset + length, value), addr_var))

                self.stack[str(len(self.stack))] = addr_var
                result.set_gas(gas_table[opcode.name])
            else:
                raise ValueError('STACK underflow')
        elif opcode.name == 'EXTCODESIZE':
            if len(self.stack) > 0:
                address = self.stack.pop(str(len(self.stack) - 1))

                code_var = BitVec('Icodesize_%s' % opcode.pc, 256)
                result.add_path_constraint(ULT(code_var, ADDRESS_BOUND_NUMBER))
                variables.add_variable(Variable('Icodesize_%s' % opcode.pc, 'address(%s).code.size' % address, code_var))

                self.stack[str(len(self.stack))] = code_var
                result.set_gas(gas_table[opcode.name])
            else:
                raise ValueError('STACK underflow')
        elif opcode.name == 'BLOCKHASH':
            if len(self.stack) > 0:
                block_num = self.stack.pop(str(len(self.stack) - 1))

                hash_var = BitVec('Ih_%s' % opcode.pc, 256)
                result.add_path_constraint(ULT(hash_var, ADDRESS_BOUND_NUMBER))
                variables.add_variable(Variable('Ih_%s' % opcode.pc, 'block.blockHash(%s)' % block_num, hash_var))

                self.stack[str(len(self.stack))] = hash_var
                result.set_gas(gas_table[opcode.name])
            else:
                raise ValueError('STACK underflow')
        elif opcode.name == 'SELFDESTRUCT':
            if len(self.stack) > 0:
                address = self.stack.pop(str(len(self.stack) - 1))

                contract_var = BitVec('Inewaccount_%s' % opcode.pc, 256)
                result.add_path_constraint(Or(contract_var==1, contract_var==0))
                variables.add_variable(Variable('Inewaccount_%s' % opcode.pc, 'selfdestruct(address(%s))' % address, contract_var))
                result.set_gas(5000 + BV2Int(If(contract_var, 25000, 0)))
            else:
                raise ValueError('STACK underflow')
        else:
            raise Exception('UNKNOWN INSTRUCTION:', opcode)
        
        return result