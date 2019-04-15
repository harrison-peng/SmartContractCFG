import six
import sha3
from z3 import *
from gas_price import gas_table
from global_vars import *

UNSIGNED_BOUND_NUMBER = 2**256 - 1
solver = Solver()


def state_simulation(instruction, state, line):
    global solver

    stack = state['Stack']
    memory = state['Memory']
    storage = state['Storage']
    instruction_set = instruction.split(' ')
    opcode = instruction_set[0]
    gas = 0
    path_constraint = ''
    gas_constraint = True
    for key, val in stack.items():
        if isinstance(val, str):
            print('[STACK]', instruction, stack)
            raise Exception
    for key, val in memory.items():
        if isinstance(val, str):
            print('[MEMORY]', instruction)
            raise Exception
    for key, val in storage.items():
        if isinstance(val, str):
            print('[STORAGE]', instruction)
            raise Exception

    if opcode in ['INVALID', 'STOP', 'REVERT', 'JUMPDEST']:
        pass
    elif opcode == 'TIMESTAMP':
        new_var_name = get_gen().gen_time_var(line)
        new_var = BitVec(new_var_name, 256)
        gas_constraint = simplify(new_var < 2**256)

        row = len(stack)
        stack[str(row)] = new_var

        # NOTE: GAS
        gas = gas_table[opcode]
    elif opcode == 'ADD':
        if len(stack) > 1:
            row = len(stack) - 1
            first = stack.pop(str(row))
            second = stack.pop(str(row - 1))

            # if isinstance(first, str):
            #     first = to_z3_symbolic(first)
            # if isinstance(second, str):
            #     second = to_z3_symbolic(second)
            # computed = first + second

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

            computed = simplify(computed) if is_expr(computed) else computed

            row = len(stack)
            stack[str(row)] = computed

            # NOTE: GAS
            gas = gas_table[opcode]
        else:
            raise ValueError('STACK underflow')
    elif opcode == 'MUL':
        if len(stack) > 1:
            row = len(stack) - 1
            first = stack.pop(str(row))
            second = stack.pop(str(row - 1))

            # if isinstance(first, int) and isinstance(second, int):
            #     computed = first * second & UNSIGNED_BOUND_NUMBER
            # else:
            #     if isinstance(first, str):
            #         first = to_z3_symbolic(first)
            #     if isinstance(second, str):
            #         second = to_z3_symbolic(second)
            #     computed = first * second

            if is_real(first) and is_symbolic(second):
                first = BitVecVal(first, 256)
            elif is_symbolic(first) and is_real(second):
                second = BitVecVal(second, 256)
            computed = first * second & UNSIGNED_BOUND_NUMBER
            computed = simplify(computed) if is_expr(computed) else computed

            row = len(stack)
            stack[str(row)] = computed

            # NOTE: GAS
            gas = gas_table[opcode]
        else:
            raise ValueError('STACK underflow')
    elif opcode == 'SUB':
        if len(stack) > 1:
            row = len(stack) - 1
            first = stack.pop(str(row))
            second = stack.pop(str(row - 1))

            # if isinstance(first, int) and isinstance(second, int):
            #     computed = first - second
            # else:
            #     if isinstance(first, str):
            #         first = to_z3_symbolic(first)
            #     if isinstance(second, str):
            #         second = to_z3_symbolic(second)
            #     computed = first - second

            if is_real(first) and is_symbolic(second):
                first = BitVecVal(first, 256)
                computed = first - second
            elif is_symbolic(first) and is_real(second):
                second = BitVecVal(second, 256)
                computed = first - second
            else:
                computed = (first - second) % (2 ** 256)
            computed = simplify(computed) if is_expr(computed) else computed

            row = len(stack)
            stack[str(row)] = computed

            # NOTE: GAS
            gas = gas_table[opcode]
        else:
            raise ValueError('STACK underflow')
    elif opcode == 'DIV':
        if len(stack) > 1:
            row = len(stack) - 1
            first = stack.pop(str(row))
            second = stack.pop(str(row - 1))

            if is_all_real(first, second):
                if second == 0:
                    computed = 0
                else:
                    first = to_unsigned(first)
                    second = to_unsigned(second)
                    computed = first // second
            else:
                first = to_symbolic(first)
                second = to_symbolic(second)
                solver.push()
                solver.add(Not(second == 0))
                if check_sat(solver) == unsat:
                    computed = 0
                else:
                    computed = UDiv(first, second)
                solver.pop()
            computed = simplify(computed) if is_expr(computed) else computed

            row = len(stack)
            stack[str(row)] = computed

            # NOTE: GAS
            gas = gas_table[opcode]
        else:
            raise ValueError('STACK underflow')
    elif opcode == 'SDIV':
        if len(stack) > 1:
            row = len(stack) - 1
            first = stack.pop(str(row))
            second = stack.pop(str(row - 1))

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
                solver.push()
                solver.add(Not(second == 0))
                if check_sat(solver) == unsat:
                    computed = 0
                else:
                    solver.push()
                    solver.add(Not(And(first == -2**255, second == -1)))
                    if check_sat(solver) == unsat:
                        computed = -2**255
                    else:
                        solver.push()
                        solver.add(first / second < 0)
                        sign = -1 if check_sat(solver) == sat else 1
                        z3_abs = lambda x: If(x >= 0, x, -x)
                        first = z3_abs(first)
                        second = z3_abs(second)
                        computed = sign * (first / second)
                        solver.pop()
                    solver.pop()
                solver.pop()
            computed = simplify(computed) if is_expr(computed) else computed

            row = len(stack)
            stack[str(row)] = computed

            # NOTE: GAS
            gas = gas_table[opcode]
        else:
            raise ValueError('STACK underflow')
    elif opcode == 'MOD':
        if len(stack) > 1:
            row = len(stack) - 1
            first = stack.pop(str(row))
            second = stack.pop(str(row - 1))

            # if isinstance(first, int) and isinstance(second, int):
            #     if second == 0:
            #         computed = 0
            #     else:
            #         first = to_unsigned(first)
            #         second = to_unsigned(second)
            #         computed = first % second & UNSIGNED_BOUND_NUMBER
            # else:
            #     if isinstance(first, str):
            #         first = to_z3_symbolic(first)
            #     if isinstance(second, str):
            #         second = to_z3_symbolic(second)
            #     computed = first % second

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

                solver.push()
                solver.add(Not(second == 0))
                if check_sat(solver) == unsat:
                    # it is provable that second is indeed equal to zero
                    computed = 0
                else:
                    computed = URem(first, second)
                solver.pop()
            computed = simplify(computed) if is_expr(computed) else computed

            row = len(stack)
            stack[str(row)] = computed

            # NOTE: GAS
            gas = gas_table[opcode]
        else:
            raise ValueError('STACK underflow')
    elif opcode == 'SMOD':
        if len(stack) > 1:
            row = len(stack) - 1
            first = stack.pop(str(row))
            second = stack.pop(str(row - 1))

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

                solver.push()
                solver.add(Not(second == 0))
                if check_sat(solver) == unsat:
                    # NOTE: it is provable that second is indeed equal to zero
                    computed = 0
                else:

                    solver.push()
                    solver.add(first < 0)  # check sign of first element
                    sign = BitVecVal(-1, 256) if check_sat(solver) == sat \
                        else BitVecVal(1, 256)
                    solver.pop()

                    z3_abs = lambda x: If(x >= 0, x, -x)
                    first = z3_abs(first)
                    second = z3_abs(second)

                    computed = sign * (first % second)
                solver.pop()

            computed = simplify(computed) if is_expr(computed) else computed
            row = len(stack)
            stack[str(row)] = computed

            # NOTE: GAS
            gas = gas_table[opcode]
        else:
            raise ValueError('STACK underflow')
    elif opcode == 'ADDMOD':
        if len(stack) > 2:
            row = len(stack) - 1
            first = stack.pop(str(row))
            second = stack.pop(str(row - 1))
            third = stack.pop(str(row - 2))

            # if is_all_real(first, second, third):
            #     if third == 0:
            #         computed = 0
            #     else:
            #         computed = (first + second) % third
            # else:
            #     if isinstance(first, str):
            #         first = to_z3_symbolic(first)
            #     if isinstance(second, str):
            #         second = to_z3_symbolic(second)
            #     if isinstance(third, str):
            #         third = to_z3_symbolic(third)
            #     computed = (first + second) % third

            if is_all_real(first, second, third):
                if third == 0:
                    computed = 0
                else:
                    computed = (first + second) % third
            else:
                first = to_symbolic(first)
                second = to_symbolic(second)
                solver.push()
                solver.add( Not(third == 0) )
                if check_sat(solver) == unsat:
                    computed = 0
                else:
                    first = ZeroExt(256, first)
                    second = ZeroExt(256, second)
                    third = ZeroExt(256, third)
                    computed = (first + second) % third
                    computed = Extract(255, 0, computed)
                solver.pop()
            computed = simplify(computed) if is_expr(computed) else computed

            row = len(stack)
            stack[row] = computed

            # NOTE: GAS
            gas = gas_table[opcode]
        else:
            raise ValueError('STACK underflow')
    elif opcode == 'MULMOD':
        if len(stack) > 2:
            row = len(stack) - 1
            first = stack.pop(str(row))
            second = stack.pop(str(row - 1))
            third = stack.pop(str(row - 2))

            # if is_all_real(first, second, third):
            #     if third == 0:
            #         computed = 0
            #     else:
            #         computed = (first * second) % third
            # else:
            #     if isinstance(first, str):
            #         first = to_z3_symbolic(first)
            #     if isinstance(second, str):
            #         second = to_z3_symbolic(second)
            #     if isinstance(third, str):
            #         third = to_z3_symbolic(third)
            #     computed = (first * second) % third

            if is_all_real(first, second, third):
                if third == 0:
                    computed = 0
                else:
                    computed = (first * second) % third
            else:
                first = to_symbolic(first)
                second = to_symbolic(second)
                solver.push()
                solver.add( Not(third == 0) )
                if check_sat(solver) == unsat:
                    computed = 0
                else:
                    first = ZeroExt(256, first)
                    second = ZeroExt(256, second)
                    third = ZeroExt(256, third)
                    computed = URem(first * second, third)
                    computed = Extract(255, 0, computed)
                solver.pop()
            computed = simplify(computed) if is_expr(computed) else computed

            row = len(stack)
            stack[str(row)] = computed

            # NOTE: GAS
            gas = gas_table[opcode]
        else:
            raise ValueError('STACK underflow')
    elif opcode == 'EXP':
        if len(stack) > 1:
            row = len(stack) - 1
            base = stack.pop(str(row))
            exponent = stack.pop(str(row - 1))

            computed = 0
            if is_all_real(base, exponent):
                # computed = pow(base, exponent)
                # row = len(stack)
                # stack[str(row)] = computed

                computed = pow(base, exponent, 2 ** 256)

                # NOTE: GAS
                if computed == 0:
                    gas = 10
                else:
                    gas = 10 + (10 * (1 + math.log(computed, 256)))
            else:
                # if isinstance(base, str):
                #     base = to_z3_symbolic(base)
                # if isinstance(exponent, str):
                #     exponent = to_z3_symbolic(exponent)
                # # FIXME: Z3
                # computed = '%s**%s' % (base, exponent)
                # row = len(stack)
                # stack[str(row)] = computed

                new_var_name = get_gen().gen_exp_var(line)
                computed = BitVec(new_var_name, 256)
                gas_constraint = simplify(computed < (2 ** 256) - 1)

                # NOTE: GAS
                if is_real(computed):
                    gas = 10 + (10 * (1 + math.log(computed, 256)))
                else:
                    gas_var = BitVec(get_gen().gen_log_var(line), 256)
                    gas = simplify(10 + (10 * (1 + gas_var)))
                    gas_constraint = simplify(gas_var < (2 ** 256) - 1)

            row = len(stack)
            stack[str(row)] = computed
        else:
            raise ValueError('STACK underflow')
    elif opcode == 'SIGNEXTEND':
        if len(stack) > 1:
            row = len(stack) - 1
            bit = stack.pop(str(row))
            second = stack.pop(str(row - 1))

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
                solver.push()
                solver.add(Not(Or(bit >= 32, bit < 0)))
                if check_sat(solver) == unsat:
                    computed = second
                else:
                    signbit_index_from_right = 8 * bit + 7
                    solver.push()
                    solver.add(second & (1 << signbit_index_from_right) == 0)
                    if check_sat(solver) == unsat:
                        computed = second | (2 ** 256 - (1 << signbit_index_from_right))
                    else:
                        computed = second & ((1 << signbit_index_from_right) - 1)
                    solver.pop()
                solver.pop()

            computed = simplify(computed) if is_expr(computed) else computed
            row = len(stack)
            stack[row] = computed

            # NOTE: GAS
            gas = gas_table[opcode]
        else:
            raise ValueError('STACK underflow')
    elif opcode == 'LT':
        if len(stack) > 1:
            row = len(stack) - 1
            first = stack.pop(str(row))
            second = stack.pop(str(row - 1))

            # if isinstance(first, int) and isinstance(second, int):
            #     first = to_unsigned(first)
            #     second = to_unsigned(second)
            #     if first < second:
            #         computed = 1
            #     else:
            #         computed = 0
            # else:
            #     if isinstance(first, int) and isinstance(second, int):
            #         first = to_unsigned(first)
            #         second = to_unsigned(second)
            #         if first < second:
            #             computed = 1
            #         else:
            #             computed = 0
            #     else:
            #         if isinstance(first, str):
            #             first = to_z3_symbolic(first)
            #         if isinstance(second, str):
            #             second = to_z3_symbolic(second)
            #
            #         computed = If(first < second, BitVecVal(1, 256), BitVecVal(0, 256))
            #         # computed = '(' + str(first) + '<' + str(second) + ')'

            if is_all_real(first, second):
                first = to_unsigned(first)
                second = to_unsigned(second)
                if first < second:
                    computed = 1
                else:
                    computed = 0
            else:
                # computed = If(ULT(first, second), BitVecVal(1, 256), BitVecVal(0, 256))
                computed = If(first < second, BitVecVal(1, 256), BitVecVal(0, 256))
            computed = simplify(computed) if is_expr(computed) else computed

            row = len(stack)
            stack[str(row)] = computed

            # NOTE: GAS
            gas = gas_table[opcode]
        else:
            raise ValueError('STACK underflow')
    elif opcode == 'GT':
        if len(stack) > 1:
            row = len(stack) - 1
            first = stack.pop(str(row))
            second = stack.pop(str(row - 1))

            # if isinstance(first, int) and isinstance(second, int):
            #     first = to_unsigned(first)
            #     second = to_unsigned(second)
            #     if first > second:
            #         computed = 1
            #     else:
            #         computed = 0
            # else:
            #     if isinstance(first, int) and isinstance(second, int):
            #         first = to_unsigned(first)
            #         second = to_unsigned(second)
            #         if first > second:
            #             computed = 1
            #         else:
            #             computed = 0
            #     else:
            #         if isinstance(first, str):
            #             first = to_z3_symbolic(first)
            #         if isinstance(second, str):
            #             second = to_z3_symbolic(second)
            #
            #         computed = If(first > second, BitVecVal(1, 256), BitVecVal(0, 256))
            #         # computed = '(' + str(first) + '>' + str(second) + ')'

            if is_all_real(first, second):
                first = to_unsigned(first)
                second = to_unsigned(second)
                if first > second:
                    computed = 1
                else:
                    computed = 0
            else:
                computed = If(first > second, BitVecVal(1, 256), BitVecVal(0, 256))
            computed = simplify(computed) if is_expr(computed) else computed

            row = len(stack)
            stack[str(row)] = computed

            # NOTE: GAS
            gas = gas_table[opcode]
        else:
            raise ValueError('STACK underflow')
    elif opcode == 'SLT':
        # FIXME: Not fully faithful to signed comparison
        if len(stack) > 1:
            row = len(stack) - 1
            first = stack.pop(row)
            second = stack.pop(row - 1)

            # if isinstance(first, int) and isinstance(second, int):
            #     first = to_signed(first)
            #     second = to_signed(second)
            #     if first < second:
            #         computed = 1
            #     else:
            #         computed = 0
            # else:
            #     if isinstance(first, str):
            #         first = to_z3_symbolic(first)
            #     if isinstance(second, str):
            #         second = to_z3_symbolic(second)
            #
            #     computed = If(first < second, BitVecVal(1, 256), BitVecVal(0, 256))
            #     # computed = '(' + str(first) + '<' + str(second) + ')'

            if is_all_real(first, second):
                first = to_signed(first)
                second = to_signed(second)
                if first < second:
                    computed = 1
                else:
                    computed = 0
            else:
                computed = If(first < second, BitVecVal(1, 256), BitVecVal(0, 256))
            computed = simplify(computed) if is_expr(computed) else computed

            row = len(stack)
            stack[str(row)] = computed

            # NOTE: GAS
            gas = gas_table[opcode]
        else:
            raise ValueError('STACK underflow')
    elif opcode == 'SGT':
        # FIXME: Not fully faithful to signed comparison
        if len(stack) > 1:
            row = len(stack) - 1
            first = stack.pop(str(row))
            second = stack.pop(str(row - 1))

            # if isinstance(first, int) and isinstance(second, int):
            #     first = to_signed(first)
            #     second = to_signed(second)
            #     if first > second:
            #         computed = 1
            #     else:
            #         computed = 0
            # else:
            #     if isinstance(first, str):
            #         first = to_z3_symbolic(first)
            #     if isinstance(second, str):
            #         second = to_z3_symbolic(second)
            #
            #     computed = If(first > second, BitVecVal(1, 256), BitVecVal(0, 256))
            #     # computed = '(' + str(first) + '>' + str(second) + ')'

            if is_all_real(first, second):
                first = to_signed(first)
                second = to_signed(second)
                if first > second:
                    computed = 1
                else:
                    computed = 0
            else:
                computed = If(first > second, BitVecVal(1, 256), BitVecVal(0, 256))
            computed = simplify(computed) if is_expr(computed) else computed

            row = len(stack)
            stack[str(row)] = computed

            # NOTE: GAS
            gas = gas_table[opcode]
        else:
            raise ValueError('STACK underflow')
    elif opcode == 'EQ':
        if len(stack) > 1:
            row = len(stack) - 1
            first = stack.pop(str(row))
            second = stack.pop(str(row - 1))

            # if isinstance(first, int) and isinstance(second, int):
            #     if first == second:
            #         computed = 1
            #     else:
            #         computed = 0
            # else:
            #     if isinstance(first, str):
            #         first = to_z3_symbolic(first)
            #     if isinstance(second, str):
            #         second = to_z3_symbolic(second)
            #
            #     computed = If(first == second, BitVecVal(1, 256), BitVecVal(0, 256))

            if is_all_real(first, second):
                if first == second:
                    computed = 1
                else:
                    computed = 0
            else:
                computed = If(first == second, BitVecVal(1, 256), BitVecVal(0, 256))
            computed = simplify(computed) if is_expr(computed) else computed

            row = len(stack)
            stack[str(row)] = computed

            # NOTE: GAS
            gas = gas_table[opcode]
        else:
            raise ValueError('STACK underflow')
    elif opcode == 'ISZERO':
        if len(stack) > 0:
            row = len(stack) - 1
            first = stack.pop(str(row))

            # if isinstance(first, int):
            #     if first == 0:
            #         computed = 1
            #     else:
            #         computed = 0
            # else:
            #     if isinstance(first, int):
            #         if first == 0:
            #             computed = 1
            #         else:
            #             computed = 0
            #     else:
            #         if isinstance(first, str):
            #             first = to_z3_symbolic(first)
            #
            #         # if isinstance(first, z3.z3.BoolRef):
            #         #     computed = Not(first)
            #         # else:
            #         computed = If(first == 0, BitVecVal(1, 256), BitVecVal(0, 256))

            if is_real(first):
                if first == 0:
                    computed = 1
                else:
                    computed = 0
            else:
                computed = If(first == 0, BitVecVal(1, 256), BitVecVal(0, 256))
            computed = simplify(computed) if is_expr(computed) else computed

            row = len(stack)
            stack[str(row)] = computed

            # NOTE: GAS
            gas = gas_table[opcode]
        else:
            raise ValueError('STACK underflow')
    elif opcode == 'AND':
        if len(stack) > 1:
            row = len(stack) - 1
            first = stack.pop(str(row))
            second = stack.pop(str(row - 1))

            computed = first & second
            computed = simplify(computed) if is_expr(computed) else computed

            row = len(stack)
            stack[str(row)] = computed

            # NOTE: GAS
            gas = gas_table[opcode]
        else:
            raise ValueError('STACK underflow')
    elif opcode == 'OR':
        if len(stack) > 1:
            row = len(stack) - 1
            first = stack.pop(str(row))
            second = stack.pop(str(row - 1))

            # if isinstance(first, int) and isinstance(second, int):
            #     computed = first | second
            # else:
            #     if isinstance(first, str):
            #         first = to_z3_symbolic(first)
            #     if isinstance(second, str):
            #         second = to_z3_symbolic(second)
            #
            #     computed = first | second

            computed = first | second
            computed = simplify(computed) if is_expr(computed) else computed

            row = len(stack)
            stack[str(row)] = computed

            # NOTE: GAS
            gas = gas_table[opcode]
        else:
            raise ValueError('STACK underflow')
    elif opcode == 'XOR':
        if len(stack) > 1:
            row = len(stack) - 1
            first = stack.pop(str(row))
            second = stack.pop(str(row - 1))

            # if isinstance(first, int) and isinstance(second, int):
            #     computed = first ^ second
            # else:
            #     computed = str(first) + '^' + str(second)

            computed = first ^ second
            computed = simplify(computed) if is_expr(computed) else computed

            row = len(stack)
            stack[str(row)] = computed

            # NOTE: GAS
            gas = gas_table[opcode]
        else:
            raise ValueError('STACK underflow')
    elif opcode == 'NOT':
        if len(stack) > 0:
            row = len(stack) - 1
            first = stack.pop(str(row))

            # if isinstance(first, int):
            #     computed = (~first) & UNSIGNED_BOUND_NUMBER
            # else:
            #     computed = '(' + '~' + str(first) + ')'

            computed = (~first) & UNSIGNED_BOUND_NUMBER
            computed = simplify(computed) if is_expr(computed) else computed

            row = len(stack)
            stack[str(row)] = computed

            # NOTE: GAS
            gas = gas_table[opcode]
        else:
            raise ValueError('STACK underflow')
    elif opcode == 'BYTE':
        if len(stack) > 1:
            row = len(stack) - 1
            first = stack.pop(str(row))
            second = stack.pop(str(row - 1))
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
                solver.push()
                solver.add(Not(Or(first >= 32, first < 0)))
                if check_sat(solver) == unsat:
                    computed = 0
                else:
                    computed = second & (255 << (8 * byte_index))
                    computed >>= (8 * byte_index)
                solver.pop()

            computed = simplify(computed) if is_expr(computed) else computed
            row = len(stack)
            stack[str(row)] = computed

            # NOTE: GAS
            gas = gas_table[opcode]
        else:
            raise ValueError('STACK underflow')
    elif opcode in ['SHA3', 'KECCAK256']:
        # FIXME: NEED To FIX
        if len(stack) > 1:
            row = len(stack) - 1
            position = stack.pop(str(row))
            to = stack.pop(str(row - 1))

            if isinstance(position, int) and isinstance(to, int):
                mem_num = (to - position)//32
                data = 0

                # if (mem_num // (2**256)) == 0:
                #     new_var_name = get_gen().gen_arbitrary_var(line)
                #     data = BitVec(new_var_name, 256)
                #     gas_constraint = simplify(data < (2 ** 256) - 1)
                # else:
                for i in range(mem_num):
                    if str(position + 32*i) in memory.keys():
                        if isinstance(memory[str(position + 32*i)], int):
                            if memory[str(position + 32*i)] != 0:
                                data += memory[str(position + 32*i)]
                        else:
                            data += memory[str(position + 32 * i)]
                        if is_expr(data):
                            data = simplify(data)
                    else:
                        new_var_name = get_gen().gen_arbitrary_var(line)
                        data = simplify(data+BitVec(new_var_name, 256))
                        gas_constraint = simplify(data < (2 ** 256) - 1)
            else:
                new_var_name = get_gen().gen_arbitrary_var(line)
                data = BitVec(new_var_name, 256)
                gas_constraint = simplify(data < (2 ** 256) - 1)

            if isinstance(data, int):
                computed = int(sha3.sha3_224(str(data).encode('utf-8')).hexdigest(), 16)
            else:
                new_var_name = get_gen().gen_sha_var(line, data)
                computed = BitVec(new_var_name, 256)
                gas_constraint = simplify(computed < (2 ** 256) - 1)
            data = simplify(data) if is_expr(data) else data

            row = len(stack)
            stack[str(row)] = computed

            # NOTE: GAS
            if isinstance(data, int):
                gas = 30 + 6 * data
            else:
                if is_expr(data):
                    gas = simplify(30 + 6 * data)
                else:
                    gas = simplify(30 + 6*BitVec('WORDSIZE', 256))
        else:
            raise ValueError('STACK underflow')
    elif opcode == 'ADDRESS':
        # NOTE: get address of currently executing account
        # TODO: handle it
        row = len(stack)
        stack[str(row)] = BitVec('Ia', 256)

        # NOTE: GAS
        gas = gas_table[opcode]
    elif opcode == 'BALANCE':
        # TODO: handle it
        if len(stack) > 0:
            row = len(stack) - 1
            address = stack.pop(str(row))

            new_var_name = get_gen().gen_balance_var(line)
            new_var = BitVec(new_var_name, 256)
            gas_constraint = simplify(new_var < (2 ** 256) - 1)

            row = len(stack)
            stack[str(row)] = new_var

            # NOTE: GAS
            gas = gas_table[opcode]
        else:
            raise ValueError('STACK underflow')
    elif opcode == 'CALLER':
        # NOTE: get caller address
        new_var_name = get_gen().gen_caller_var(line)
        new_var = BitVec(new_var_name, 256)
        gas_constraint = simplify(new_var < (2 ** 160))

        row = len(stack)
        stack[str(row)] = new_var

        # NOTE: GAS
        gas = gas_table[opcode]
    elif opcode == "ORIGIN":
        # NOTE: get execution origination address
        new_var_name = get_gen().gen_origin_var(line)
        new_var = BitVec(new_var_name, 256)
        gas_constraint = simplify(new_var < (2 ** 256) - 1)

        row = len(stack)
        stack[str(row)] = new_var

        # NOTE: GAS
        gas = gas_table[opcode]
    elif opcode == 'CALLVALUE':
        # NOTE: get value of this transaction
        # TODO: handle it
        new_var_name = get_gen().gen_value_var(line)
        new_var = BitVec(new_var_name, 256)
        gas_constraint = simplify(new_var < (2 ** 256) - 1)

        row = len(stack)
        stack[str(row)] = new_var

        # NOTE: GAS
        gas = gas_table[opcode]
    elif opcode == 'CALLDATALOAD':
        # NOTE: from input data from environment
        if len(stack) > 0:
            row = len(stack) - 1
            position = stack.pop(str(row))

            # row = len(stack)
            # if is_real(position):
            #     stack[str(row)] = to_z3_symbolic('MSGDATA[%s:%s]' % (position, position + 32))
            # else:
            #     stack[str(row)] = to_z3_symbolic('MSGDATA[%s:%s]' % (str(position), '%s+32' % position))

            new_var_name = get_gen().gen_data_var(line)
            new_var = BitVec(new_var_name, 256)
            gas_constraint = simplify(new_var < (2 ** 256) - 1)

            row = len(stack)
            stack[str(row)] = new_var

            # NOTE: GAS
            gas = gas_table[opcode]
        else:
            raise ValueError('STACK underflow')
    elif opcode == 'CALLDATASIZE':
        new_var_name = get_gen().gen_data_size(line)
        new_var = BitVec(new_var_name, 256)
        gas_constraint = simplify(new_var < (2 ** 256) - 1)

        row = len(stack)
        stack[str(row)] = new_var

        # NOTE: GAS
        gas = gas_table[opcode]
    elif opcode == "CALLDATACOPY":
        # NOTE: Copy input data to memory
        if len(stack) > 2:
            row = len(stack) - 1
            memory_position = stack.pop(str(row))
            data_position = stack.pop(str(row - 1))
            num_bytes = stack.pop(str(row - 2))

            # TODO: handle gas and memory
            # NOTE: GAS
            if is_real(num_bytes):
                gas = 2 + 3 * num_bytes
            else:
                gas = simplify(2 + 3 * num_bytes)
                # gas = '2+3*%s' % num_bytes
        else:
            raise ValueError('STACK underflow')
    elif opcode == 'CODESIZE':
        # TODO: handle it
        row = len(stack)
        stack[str(row)] = to_z3_symbolic('CODESIZE')

        # NOTE: GAS
        gas = gas_table[opcode]
    elif opcode == 'CODECOPY':
        if len(stack) > 2:
            row = len(stack) - 1
            memory_position = stack.pop(str(row))
            code_position = stack.pop(str(row - 1))
            num_bytes = stack.pop(str(row - 2))

            # TODO: handle gas and memory
            # NOTE: GAS
            if is_real(num_bytes):
                gas = 2 + 3 * num_bytes
            else:
                gas = simplify(2 + 3 * num_bytes)
        else:
            raise ValueError('STACK underflow')
    elif opcode == 'GASPRICE':
        new_var_name = get_gen().gen_gas_price_var(line)
        new_var = BitVec(new_var_name, 256)
        gas_constraint = simplify(new_var < (2 ** 256) - 1)

        row = len(stack)
        stack[str(row)] = new_var

        # NOTE: GAS
        gas = gas_table[opcode]
    elif opcode == 'RETURNDATACOPY':
        if len(stack) > 2:
            row = len(stack) - 1
            z = stack.pop(str(row))
            y = stack.pop(str(row - 1))
            x = stack.pop(str(row - 2))

            # TODO: handle gas and memory
            # NOTE: GAS
            if is_real(x):
                gas = 2 + 3 * x
            else:
                gas = simplify(2 + 3 * x)
                # gas = '2+3*%s' % x
        else:
            raise ValueError('STACK underflow')
    elif opcode == 'RETURNDATASIZE':
        # TODO: handle it
        row = len(stack)
        stack[str(row)] = to_z3_symbolic('RETURNDATASIZE')

        # NOTE: GAS
        gas = gas_table[opcode]
    elif opcode == 'NUMBER':
        # NOTE: information from block header
        # TODO: handle it
        row = len(stack)
        stack[str(row)] = to_z3_symbolic('BLOCKNUMBER')

        # NOTE: GAS
        gas = gas_table[opcode]
    elif opcode == 'POP':
        if len(stack) > 0:
            row = len(stack) - 1
            stack.pop(str(row))

            # NOTE: GAS
            gas = gas_table[opcode]
        else:
            raise ValueError('STACK underflow')
    elif opcode == 'MLOAD':
        if len(stack) > 0:
            row = len(stack) - 1
            address = stack.pop(str(row))

            value = None
            for key, val in memory.items():
                if str(address) == str(key):
                    value = val

            if value is None:
                if is_real(address):
                    try:
                        value = memory[address]
                    except:
                        # value = to_z3_symbolic('MEMORY[%s:%s]' % (address, address + 32))
                        # value = to_z3_symbolic('MEMORY[%s]' % address)
                        new_var_name = get_gen().gen_mem_var(line)
                        value = BitVec(new_var_name, 256)
                        gas_constraint = simplify(value < (2 ** 256) - 1)
                else:
                    # value = to_z3_symbolic('MEMORY[%s:%s]' % (address, str(address) + '+32'))
                    # value = to_z3_symbolic('MEMORY[%s]' % address)
                    new_var_name = get_gen().gen_mem_var(line)
                    value = BitVec(new_var_name, 256)
                    gas_constraint = simplify(value < (2 ** 256) - 1)

            row = len(stack)
            stack[str(row)] = value

            # NOTE: GAS
            gas = gas_table[opcode]
        else:
            raise ValueError('STACK underflow')
    elif opcode == 'MSTORE':
        if len(stack) > 1:
            row = len(stack) - 1
            address = stack.pop(str(row))
            value = stack.pop(str(row - 1))
            # address = str(address).replace('+\n', '+')
            memory[str(address)] = value

            # NOTE: GAS
            gas = gas_table[opcode]
        else:
            raise ValueError('STACK underflow')
    elif opcode == 'SLOAD':
        if len(stack) > 0:
            row = len(stack) - 1
            address = stack.pop(str(row))

            if len(storage) == 0:
                value = 0
            else:
                value = None
                for key, val in storage.items():
                    if str(key) == str(address):
                        value = val

                row = len(stack)
                if value is None:
                    new_var_name = get_gen().gen_owner_store_var(line)
                    value = BitVec(new_var_name, 256)
                    gas_constraint = simplify(value < (2 ** 256) - 1)
            stack[str(row)] = value

            # NOTE: GAS
            gas = gas_table[opcode]
        else:
            raise ValueError('STACK underflow')
    elif opcode == 'SSTORE':
        if len(stack) > 1:
            row = len(stack) - 1
            address = stack.pop(str(row))
            value = stack.pop(str(row - 1))
            storage[str(address)] = value

            if is_all_real(address, value):
                if address == 0 and value != 0:
                    gas = 20000
                else:
                    gas = 5000
            else:
                if is_real(address) and address != 0:
                    gas = 5000
                elif is_real(value) and value == 0:
                    gas = 5000
                else:
                    # gas = '((%s != 0) && (%s == 0)) ? 20000 : 5000' % (str(value), str(address))
                    gas = simplify(If(And(Not(value == 0), (address == 0), True), BitVecVal(20000, 256), BitVecVal(5000, 256)))

        else:
            raise ValueError('STACK underflow')
    elif opcode == 'JUMP':
        if not (len(instruction_set) > 1 and instruction_set[1] == '[out]'):
            if len(stack) > 0:
                row = len(stack) - 1
                stack.pop(str(row))

                # NOTE: GAS
                gas = gas_table[opcode]
            else:
                raise ValueError('STACK underflow')
    elif opcode == 'JUMPI':
        if len(stack) > 1:
            row = len(stack) - 1
            address = stack.pop(str(row))
            constraint = stack.pop(str(row - 1))

            # NOTE: Path Constraint
            path_constraint = constraint

            # NOTE: GAS
            gas = gas_table[opcode]

            # TODO: handle path constraint
        else:
            raise ValueError('STACK underflow')
    elif opcode == 'GAS':
        new_var_name = get_gen().gen_gas_var(line)
        new_var = BitVec(new_var_name, 256)
        gas_constraint = simplify(new_var < (2 ** 256) - 1)

        row = len(stack)
        stack[str(row)] = new_var

        # NOTE: GAS
        gas = gas_table[opcode]
    elif opcode.startswith('PUSH', 0):
        # NOTE: this is a push instruction
        pushed_value = ''
        if len(instruction_set) > 1:
            if instruction_set[1] == '[tag]':
                pushed_value = int(instruction_set[2])
            else:
                pushed_value = int(str(instruction_set[1]), 16)
                # try:
                #     pushed_value = int(instruction_set[1])
                #     # print('[PP]:', pushed_value, hex(int(str(pushed_value), 16)))
                # except ValueError:
                #     # print('[INS]:', instruction_set)
                #     if len(instruction_set[1]) > 4:
                #         pushed_value = str(instruction_set[1])
                #     elif instruction_set[1] == 'data':
                #         print('[DATA]:', instruction_set)
                #         if len(instruction_set[1]) > 4:
                #             pushed_value = str(instruction_set[2])
                #     else:
                #         pushed_value = int(instruction_set[1], 16)
        else:
            if instruction_set[0] == 'PUSHDEPLOYADDRESS':
                new_var_name = get_gen().gen_arbitrary_address_var(line)
                pushed_value = BitVec(new_var_name, 256)
                gas_constraint = simplify(pushed_value < (2 ** 256) - 1)
        row = len(stack)
        stack[str(row)] = pushed_value

        # NOTE: GAS
        gas = gas_table['PUSH']
    elif opcode.startswith('DUP', 0):
        position = len(stack) - int(opcode[3:], 10)
        if position >= 0:
            duplicate_value = stack[str(position)]
            row = len(stack)
            stack[str(row)] = duplicate_value

            # NOTE: GAS
            gas = gas_table['DUP']
        else:
            return None, None, None, None
            # raise ValueError('STACK underflow')
    elif opcode.startswith('SWAP', 0):
        position = len(stack) - 1 - int(opcode[4:], 10)
        if len(stack) > position:
            temp_value = stack[str(position)]
            row = len(stack) - 1
            stack[str(position)] = stack[str(row)]
            stack[str(row)] = temp_value

            # NOTE: GAS
            gas = gas_table['SWAP']
        else:
            raise ValueError('STACK underflow')
    elif opcode in ('LOG0', 'LOG1', 'LOG2', 'LOG3', 'LOG4'):
        num_of_pops = 2 + int(opcode[3:])
        if len(stack) >= num_of_pops:
            count = 0
            gas = 0
            while num_of_pops > 0:
                num_of_pops -= 1
                row = len(stack) - 1
                pop_value = stack.pop(str(row))

                # NOTE: GAS
                if count == 1:
                    gas = (int(opcode[3:]) + 1) * 375 + (8 * pop_value)
                    # if isinstance(pop_value, int):
                    #     gas = '%s+(8*%s)' % (str((int(opcode[3:]) + 1) * 375), pop_value)
                    # else:
                    #     gas = (int(opcode[3:]) + 1) * 375 + (8 * pop_value)
        else:
            raise ValueError('STACK underflow')
    elif opcode == 'CALL':
        # TODO: Need to handle miu_i
        if len(stack) > 6:
            row = len(stack) - 1
            out_gas = stack.pop(str(row))
            recipient = stack.pop(str(row - 1))
            out_wei = stack.pop(str(row - 2))
            in_value = stack.pop(str(row - 3))
            in_size = stack.pop(str(row - 4))
            out_value = stack.pop(str(row - 5))
            out_size = stack.pop(str(row - 6))

            row = len(stack)
            stack[str(row)] = BitVec('CallReturn', 256)

            # NOTE: GAS
            # TODO: handle gas
            gas = gas_table[opcode]
        else:
            raise ValueError('STACK underflow')
    elif opcode == 'CALLCODE':
        if len(stack) > 6:
            row = len(stack) - 1
            out_gas = stack.pop(str(row))
            recipient = stack.pop(str(row - 1))
            out_wei = stack.pop(str(row - 2))
            in_value = stack.pop(str(row - 3))
            in_size = stack.pop(str(row - 4))
            out_value = stack.pop(str(row - 5))
            out_size = stack.pop(str(row - 6))

            new_var_name = get_gen().gen_caller_var(line)
            new_var = BitVec(new_var_name, 256)
            gas_constraint = simplify(new_var < (2 ** 256) - 1)

            row = len(stack)
            stack[str(row)] = new_var

            # NOTE: GAS
            # TODO: handle gas
            gas = gas_table[opcode]
        else:
            raise ValueError('STACK underflow')
    elif opcode in ['DELEGATECALL', 'STATICCALL']:
        if len(stack) > 2:
            row = len(stack) - 1
            out_gas = stack.pop(str(row))
            recipient = stack.pop(str(row - 1))
            in_value = stack.pop(str(row - 2))
            in_size = stack.pop(str(row - 3))
            out_value = stack.pop(str(row - 4))
            out_size = stack.pop(str(row - 5))

            new_var_name = get_gen().gen_arbitrary_var(line)
            new_var = BitVec(new_var_name, 256)
            gas_constraint = simplify(new_var < (2 ** 256) - 1)

            row = len(stack)
            stack[str(row)] = new_var

            # NOTE: GAS
            # TODO: handle gas
            gas = gas_table[opcode]
        else:
            raise ValueError('STACK underflow')
    elif opcode == 'RETURN':
        # TODO: Need to handle miu_i
        if len(stack) > 1:
            row = len(stack) - 1
            stack.pop(str(row))
            stack.pop(str(row - 1))

            # NOTE: GAS
            gas = gas_table[opcode]
        else:
            raise ValueError('STACK underflow')
    elif opcode == 'CREATE':
        if len(stack) > 2:
            row = len(stack) - 1
            wei = stack.pop(str(row))
            position = stack.pop(str(row - 1))
            length = stack.pop(str(row - 2))

            new_var_name = get_gen().gen_arbitrary_var(line)
            new_var = BitVec(new_var_name, 256)
            gas_constraint = simplify(new_var < (2 ** 256) - 1)

            row = len(stack)
            stack[str(row)] = new_var

            # NOTE: GAS
            gas = gas_table[opcode]
        else:
            raise ValueError('STACK underflow')
    elif opcode == 'EXTCODESIZE':
        if len(stack) > 0:
            row = len(stack) - 1
            address = stack.pop(str(row))

            new_var_name = get_gen().gen_code_size_var(address, line)
            new_var = BitVec(new_var_name, 256)
            gas_constraint = simplify(new_var < (2 ** 256) - 1)

            row = len(stack)
            stack[str(row)] = new_var

            # NOTE: GAS
            gas = gas_table[opcode]
        else:
            raise ValueError('STACK underflow')
    elif opcode == 'BLOCKHASH':
        if len(stack) > 0:
            row = len(stack) - 1
            block_num = stack.pop(str(row))

            new_var_name = get_gen().gen_hash_var(block_num, line)
            new_var = BitVec(new_var_name, 256)
            gas_constraint = simplify(new_var < (2 ** 256) - 1)
            row = len(stack)
            stack[str(row)] = new_var

            # NOTE: GAS
            gas = gas_table[opcode]
        else:
            raise ValueError('STACK underflow')
    elif opcode == 'SELFDESTRUCT':
        if len(stack) > 0:
            row = len(stack) - 1
            stack.pop(str(row))

            # NOTE: GAS
            new_var = Bool('Inewaccount_%s' % line)
            gas = 5000 + If(new_var, 25000, 0)
        else:
            raise ValueError('STACK underflow')
    else:
        raise Exception('UNKNOWN INSTRUCTION:', opcode)

    if isinstance(gas, float):
        gas = int(round(gas))

    return state, gas, path_constraint, gas_constraint


def to_z3_symbolic(var):
    return BitVec(str(var), 256)


def to_unsigned(number):
    if number < 0:
        return number + 2**256
    return number


def to_signed(number):
    if number > 2**(256 - 1):
        return (2**256 - number) * (-1)
    else:
        return number


def is_symbolic(value):
    return not isinstance(value, six.integer_types)


def is_all_real(*args):
    for element in args:
        if is_symbolic(element):
            return False
    return True


def to_symbolic(number):
    if is_real(number):
        return BitVecVal(number, 256)
    return number


def is_real(value):
    return isinstance(value, six.integer_types)


def check_sat(solver, pop_if_exception=True):
    try:
        ret = solver.check()
        if ret == unknown:
            raise Z3Exception(solver.reason_unknown())
    except Exception as e:
        if pop_if_exception:
            solver.pop()
        raise e
    return ret
