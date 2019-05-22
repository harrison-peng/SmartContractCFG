import sha3
from gas_price import gas_table
from global_vars import *
from global_constants import *
from z3_func import *

solver = Solver()


def state_simulation(instruction, state, line, prev_jumpi_ins):
    global solver

    stack = state['Stack']
    memory = state['Memory']
    storage = state['Storage']
    instruction_set = instruction.split(' ')
    opcode = instruction_set[0]
    gas = 0
    path_constraint = ''
    gas_constraint = True
    var_constraint = True
    next_tag = None
    for key, val in stack.items():
        if isinstance(val, str):
            print('[STACK]', instruction, stack)
            raise Exception
        elif isinstance(val, z3.z3.BitVecNumRef):
            # print('[STACK]:', val)
            stack[key] = val.as_long()
    for key, val in memory.items():
        if isinstance(val, str):
            print('[MEMORY]', instruction)
            raise Exception
    for key, val in storage.items():
        if isinstance(val, str):
            print('[STORAGE]', instruction)
            raise Exception

    if 'ins' in prev_jumpi_ins.keys() and opcode in ['LT', 'GT', 'EQ', 'ISZERO']:
        prev_jumpi_ins['ins'] = opcode
        row = len(stack) - 1
        prev_jumpi_ins['s1'] = stack[str(row)]
        if opcode == 'ISZERO':
            prev_jumpi_ins['s2'] = None
        else:
            prev_jumpi_ins['s2'] = simplify(stack[str(row - 1)]) if is_expr(stack[str(row - 1)]) else stack[str(row - 1)]
    elif 'ins' in prev_jumpi_ins.keys() and len(state['Stack']) > 0 and opcode not in ['JUMPI', 'PUSH']:
        prev_jumpi_ins['ins'] = opcode
        row = len(stack) - 1
        prev_jumpi_ins['s1'] = simplify(stack[str(row)]) if is_expr(stack[str(row)]) else stack[str(row)]
        prev_jumpi_ins['s2'] = None

    if opcode in ['INVALID', 'STOP', 'REVERT', 'JUMPDEST']:
        pass
    elif opcode == 'TIMESTAMP':
        new_var_name = get_gen().gen_time_var(line)
        new_var = BitVec(new_var_name, 256)
        gas_constraint = add_gas_constraint(new_var, UNSIGNED_BOUND_NUMBER)

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

            if is_real(first) and is_symbolic(second):
                first = BitVecVal(first, 256)
                computed = first - second
            elif is_symbolic(first) and is_real(second):
                second = BitVecVal(second, 256)
                computed = first - second
            else:
                computed = (first - second) % (2 ** 256)
            # print('[SUB-1]:', computed)
            computed = simplify(computed) if is_expr(computed) else computed
            # print('[SUB-2]:', computed)

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
                # first = to_symbolic(first)
                # second = to_symbolic(second)
                # solver.push()
                # solver.add(Not(second == 0))
                # if check_sat(solver) == unsat:
                #     computed = 0
                # else:
                #     computed = UDiv(first, second)
                # solver.pop()
                if is_real(second):
                    computed = first / second
                else:
                    computed = If(second == 0, 0, first/second)
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
                computed = pow(base, exponent, 2 ** 256)

                # NOTE: GAS
                if computed == 0:
                    gas = 10
                else:
                    gas = 10 + 10 * (1 + math.log(computed, 256))
            else:
                new_var_name = get_gen().gen_exp_var(line)
                computed = BitVec(new_var_name, 256)
                gas_constraint = add_gas_constraint(computed, UNSIGNED_BOUND_NUMBER)

                if not var_in_var_table(new_var_name):
                    add_var_table(new_var_name, 'EXP(%s, %s)' % (base, exponent))

                # NOTE: GAS
                if is_real(computed):
                    gas = 10 + 10 * (1 + math.log(computed, 256))
                else:
                    if isinstance(base, int) and base == 256:
                        if is_bv(exponent):
                            gas = simplify(10 + (10 * (1 + BV2Int(exponent))))
                        else:
                            gas = simplify(10 + (10 * (1 + exponent)))
                    else:
                        gas_var = BitVec(get_gen().gen_log_var(line), 256)
                        gas = simplify(10 + (10 * (1 + BV2Int(gas_var))))
                        gas_constraint = add_gas_constraint(gas_var, BYTE_BOUND_NUMBER)

                        if not var_in_var_table(gas_var):
                            add_var_table(gas_var, 'log256(%s)' % computed)

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

            if first == second:
                computed = 0
                lt_loop_format = 0
            else:
                if is_all_real(first, second):
                    first = to_unsigned(first)
                    second = to_unsigned(second)
                    if first < second:
                        computed = 1
                    else:
                        computed = 0
                else:
                    computed = If(ULT(first, second), BitVecVal(1, 256), BitVecVal(0, 256))
                    # print('[LT]:', computed)
                    # computed = If(first < second, BitVecVal(1, 256), BitVecVal(0, 256))
                # computed = simplify(computed) if is_expr(computed) else computed

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

            if is_all_real(first, second):
                first = to_unsigned(first)
                second = to_unsigned(second)
                if first > second:
                    computed = 1
                else:
                    computed = 0
            else:
                computed = If(UGT(first, second), BitVecVal(1, 256), BitVecVal(0, 256))
                # computed = If(first > second, BitVecVal(1, 256), BitVecVal(0, 256))
            # computed = simplify(computed) if is_expr(computed) else computed

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
        if len(stack) > 1:
            row = len(stack) - 1
            first = stack.pop(str(row))
            second = stack.pop(str(row - 1))

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

            if is_all_real(first, second):
                if first == second:
                    computed = 1
                else:
                    computed = 0
            else:
                computed = If(first == second, BitVecVal(1, 256), BitVecVal(0, 256))
            # computed = simplify(computed) if is_expr(computed) else computed

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

            if is_real(first):
                if first == 0:
                    computed = 1
                else:
                    computed = 0
            else:
                computed = If(first == 0, BitVecVal(1, 256), BitVecVal(0, 256))
            # computed = simplify(computed) if is_expr(computed) else computed

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

            if isinstance(first, int) and first == 1461501637330902918203684832716283019655932542975:
                computed = second
                if is_expr(second):
                    gas_constraint = add_gas_constraint(computed, ADDRESS_BOUND_NUMBER)
            elif isinstance(second, int) and second == 1461501637330902918203684832716283019655932542975:
                computed = first
                if is_expr(first):
                    gas_constraint = add_gas_constraint(computed, ADDRESS_BOUND_NUMBER)
            else:
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
        if len(stack) > 1:
            row = len(stack) - 1
            position = stack.pop(str(row))
            length = stack.pop(str(row - 1))
            # print('[KEC]:', line, position, length)

            if isinstance(position, int) and isinstance(length, int):
                mem_num = length//32
                data = 0

                for i in range(mem_num):
                    if str(position + 32*i) in memory.keys():
                        if isinstance(memory[str(position + 32*i)], int):
                            if memory[str(position + 32*i)] != 0:
                                data += memory[str(position + 32*i)]
                        else:
                            data += memory[str(position + 32 * i)]
                            data = simplify(data) if is_expr(data) else data
                    else:
                        new_var_name = get_gen().gen_mem_var(line)
                        data = simplify(data+BitVec(new_var_name, 256))
                        gas_constraint = add_gas_constraint(data, UNSIGNED_BOUND_NUMBER)

                        if not var_in_var_table(new_var_name):
                            add_var_table(new_var_name, 'memory[%s:%s+32]' % (i, i))
            else:
                new_var_name = get_gen().gen_sha_var(line)
                data = BitVec(new_var_name, 256)
                gas_constraint = add_gas_constraint(data, UNSIGNED_BOUND_NUMBER)

                if not var_in_var_table(new_var_name):
                    add_var_table(new_var_name, 'SHA3(memory[%s:%s])' % (position, position + length))

            if isinstance(data, int):
                computed = int(sha3.sha3_224(str(data).encode('utf-8')).hexdigest(), 16)
            else:
                # NOTE: Check if sym var is already created or not
                sha3_var_exist = False
                var_name = None
                for key, val in get_var_table().items():
                    if val == 'SHA3(%s)' % data:
                        var_name = key
                        sha3_var_exist = True
                        break

                if sha3_var_exist:
                    computed = BitVec(var_name, 256)
                    gas_constraint = add_gas_constraint(computed, UNSIGNED_BOUND_NUMBER)
                else:
                    new_var_name = get_gen().gen_sha_var(line)
                    computed = BitVec(new_var_name, 256)
                    gas_constraint = add_gas_constraint(computed, UNSIGNED_BOUND_NUMBER)

                    if not var_in_var_table(new_var_name):
                        add_var_table(new_var_name, 'SHA3(%s)' % data)
            data = simplify(data) if is_expr(data) else data

            row = len(stack)
            stack[str(row)] = computed

            # NOTE: GAS
            if isinstance(length, int):
                gas = 30 + 6 * ((len(hex(length)) - 2)/4)
            else:
                if str(data) == 'Ia_caller':
                    gas = 150
                else:
                    new_var_name = get_gen().gen_sha_word_size(str(data).split('_')[1])
                    new_var = BitVec(new_var_name, 256)
                    gas = simplify(30 + 6 * BV2Int(new_var))
                    gas_constraint = add_gas_constraint(new_var, BYTE_BOUND_NUMBER)

                    if not var_in_var_table(new_var_name):
                        add_var_table(new_var_name, 'The word size of %s' % data)
        else:
            raise ValueError('STACK underflow')
    elif opcode == 'ADDRESS':
        # NOTE: get address of currently executing account
        # TODO: handle it
        new_var_name = 'Ia'
        new_var = BitVec(new_var_name, 256)
        gas_constraint = add_gas_constraint(new_var, UNSIGNED_BOUND_NUMBER)

        if not var_in_var_table(new_var_name):
            add_var_table(new_var_name, 'address(this) (address of the executing contract)')

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
            gas_constraint = add_gas_constraint(new_var, UNSIGNED_BOUND_NUMBER)

            if not var_in_var_table(new_var_name):
                add_var_table(new_var_name, 'address(%s).balance' % address)

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
        gas_constraint = add_gas_constraint(new_var, ADDRESS_BOUND_NUMBER)

        if not var_in_var_table(new_var_name):
            add_var_table(new_var_name, 'msg.caller (caller address)')

        row = len(stack)
        stack[str(row)] = new_var

        # NOTE: GAS
        gas = gas_table[opcode]
    elif opcode == "ORIGIN":
        # NOTE: get execution origination address
        new_var_name = get_gen().gen_origin_var(line)
        new_var = BitVec(new_var_name, 256)
        gas_constraint = add_gas_constraint(new_var, UNSIGNED_BOUND_NUMBER)

        if not var_in_var_table(new_var_name):
            add_var_table(new_var_name, 'tx.origin (transaction origin address)')

        row = len(stack)
        stack[str(row)] = new_var

        # NOTE: GAS
        gas = gas_table[opcode]
    elif opcode == 'CALLVALUE':
        # NOTE: get value of this transaction
        # TODO: handle it
        new_var_name = get_gen().gen_value_var(line)
        new_var = BitVec(new_var_name, 256)
        gas_constraint = add_gas_constraint(new_var, UNSIGNED_BOUND_NUMBER)

        if not var_in_var_table(new_var_name):
            add_var_table(new_var_name, 'msg.value')

        row = len(stack)
        stack[str(row)] = new_var

        # NOTE: GAS
        gas = gas_table[opcode]
    elif opcode == 'CALLDATALOAD':
        # NOTE: from input data from environment
        if len(stack) > 0:
            row = len(stack) - 1
            position = stack.pop(str(row))

            # NOTE: Check if the sym var of msg.data is already created or not
            data_var_exist = False
            var_name = None
            for key, val in get_var_table().items():
                if isinstance(position, int):
                    if val == 'msg.data[%s:%s]' % (position, position + 32):
                        var_name = key
                        data_var_exist = True
                        break
                else:
                    if val == 'msg.data[%s:%s]' % (position, simplify(position+32)):
                        var_name = key
                        data_var_exist = True
                        break

            if data_var_exist:
                new_var = BitVec(var_name, 256)
                gas_constraint = add_gas_constraint(new_var, UNSIGNED_BOUND_NUMBER)
                set_same_var(get_gen().gen_data_var(line), var_name)
            else:
                new_var_name = get_gen().gen_data_var(line)
                new_var = BitVec(new_var_name, 256)
                gas_constraint = add_gas_constraint(new_var, UNSIGNED_BOUND_NUMBER)

                if not var_in_var_table(new_var_name):
                    if isinstance(position, int):
                        add_var_table(new_var_name, 'msg.data[%s:%s]' % (position, position + 32))
                    else:
                        add_var_table(new_var_name, 'msg.data[%s:%s]' % (position, simplify(position+32)))

            row = len(stack)
            stack[str(row)] = new_var

            # NOTE: GAS
            gas = gas_table[opcode]
        else:
            raise ValueError('STACK underflow')
    elif opcode == 'CALLDATASIZE':
        new_var_name = get_gen().gen_data_size(line)
        new_var = BitVec(new_var_name, 256)
        gas_constraint = add_gas_constraint(new_var, BYTE_BOUND_NUMBER)

        if not var_in_var_table(new_var_name):
            add_var_table(new_var_name, 'msg.data.size')

        row = len(stack)
        stack[str(row)] = new_var

        # NOTE: GAS
        gas = gas_table[opcode]
    elif opcode == "CALLDATACOPY":
        # NOTE: Copy input data to memory
        if len(stack) > 2:
            row = len(stack) - 1
            mem_p = stack.pop(str(row))
            msg_p = stack.pop(str(row - 1))
            num_bytes = stack.pop(str(row - 2))

            new_var_name = get_gen().gen_data_var(line)
            new_var = BitVec(new_var_name, 256)
            var_constraint = add_gas_constraint(new_var, UNSIGNED_BOUND_NUMBER)
            memory[str(mem_p)] = new_var

            if not var_in_var_table(new_var_name):
                add_var_table(new_var_name, 'msg.data[%s:%s+%s]' % (msg_p, msg_p, num_bytes))

            # NOTE: GAS
            if is_real(num_bytes):
                gas = 2 + 3 * (len(hex(num_bytes))-2)
            else:
                new_var_name = get_gen().gen_sha_word_size(str(num_bytes).split('_')[1])
                new_var = BitVec(new_var_name, 256)
                gas = simplify(2 + 3 * BV2Int(new_var))
                gas_constraint = add_gas_constraint(new_var, BYTE_BOUND_NUMBER)

                if not var_in_var_table(new_var_name):
                    add_var_table(new_var_name, 'The word size of %s' % num_bytes)
        else:
            raise ValueError('STACK underflow')
    elif opcode == 'CODESIZE':
        new_var_name = get_gen().gen_data_size(line)
        new_var = BitVec(new_var_name, 256)
        gas_constraint = add_gas_constraint(new_var, UNSIGNED_BOUND_NUMBER)

        if not var_in_var_table(new_var_name):
            add_var_table(new_var_name, 'address(this).code.size')

        row = len(stack)
        stack[str(row)] = to_z3_symbolic(new_var)

        # NOTE: GAS
        gas = gas_table[opcode]
    elif opcode == 'CODECOPY':
        if len(stack) > 2:
            row = len(stack) - 1
            mem_p = stack.pop(str(row))
            msg_p = stack.pop(str(row - 1))
            num_bytes = stack.pop(str(row - 2))

            new_var_name = get_gen().gen_code_var(line)
            new_var = BitVec(new_var_name, 256)
            gas_constraint = add_gas_constraint(new_var, UNSIGNED_BOUND_NUMBER)
            memory[str(mem_p)] = new_var

            if not var_in_var_table(new_var_name):
                add_var_table(new_var_name, 'address(this).code[%s:%s+%s]' % (mem_p, msg_p, num_bytes))

            # NOTE: GAS
            if is_real(num_bytes):
                gas = 2 + 3 * (len(hex(num_bytes)) - 2)
            else:
                new_var_name = get_gen().gen_sha_word_size(str(num_bytes).split('_')[1])
                new_var = BitVec(new_var_name, 256)
                gas = simplify(30 + 6 * BV2Int(new_var))
                gas_constraint = add_gas_constraint(new_var, BYTE_BOUND_NUMBER)

                if not var_in_var_table(new_var_name):
                    add_var_table(new_var_name, 'The word size of %s' % num_bytes)
        else:
            raise ValueError('STACK underflow')
    elif opcode == 'GASPRICE':
        new_var_name = get_gen().gen_gas_price_var(line)
        new_var = BitVec(new_var_name, 256)
        gas_constraint = add_gas_constraint(new_var, UNSIGNED_BOUND_NUMBER)

        if not var_in_var_table(new_var_name):
            add_var_table(new_var_name, 'tx.gasprice')

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

            new_var_name = get_gen().gen_data_var(line)
            new_var = BitVec(new_var_name, 256)
            var_constraint = add_gas_constraint(new_var, UNSIGNED_BOUND_NUMBER)
            memory[str(z)] = new_var

            if not var_in_var_table(new_var_name):
                add_var_table(new_var_name, 'RETURNDATA[%s:%s+%s]' % (z, y, x))

            # NOTE: GAS
            if is_real(x):
                gas = 2 + 3 * (len(hex(x)) - 2)
            else:
                new_var_name = get_gen().gen_sha_word_size(str(x).split('_')[1])
                new_var = BitVec(new_var_name, 256)
                gas = simplify(30 + 6 * BV2Int(new_var))
                gas_constraint = add_gas_constraint(new_var, BYTE_BOUND_NUMBER)

                if not var_in_var_table(new_var_name):
                    add_var_table(new_var_name, 'The word size of %s' % x)
        else:
            raise ValueError('STACK underflow')
    elif opcode == 'RETURNDATASIZE':
        # TODO: handle it
        new_var_name = get_gen().gen_data_size(line)
        new_var = BitVec(new_var_name, 256)

        if not var_in_var_table(new_var_name):
            add_var_table(new_var_name, 'return data size')

        row = len(stack)
        stack[str(row)] = to_z3_symbolic(new_var)

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
                    if address in memory.keys():
                        value = memory[address]
                    else:
                        sym_key = False
                        for key in memory.keys():
                            if is_expr(key):
                                sym_key = True
                                break
                        if sym_key:
                            # NOTE: Check if sym var is already created or not
                            mem_var_exist = False
                            var_name = None
                            for key, val in get_var_table().items():
                                if val == 'memory[%s:%s], %s' % (address, address + 32, memory):
                                    var_name = key
                                    mem_var_exist = True
                                    break

                            if mem_var_exist:
                                value = BitVec(var_name, 256)
                                gas_constraint = add_gas_constraint(value, UNSIGNED_BOUND_NUMBER)
                            else:
                                new_var_name = get_gen().gen_mem_var(line)
                                value = BitVec(new_var_name, 256)
                                gas_constraint = add_gas_constraint(value, UNSIGNED_BOUND_NUMBER)

                                if not var_in_var_table(new_var_name):
                                    add_var_table(new_var_name, 'memory[%s:%s], %s' % (address, address + 32, memory))
                        else:
                            value = 0
                else:
                    # NOTE: Check if sym var is already created or not
                    mem_var_exist = False
                    var_name = None
                    for key, val in get_var_table().items():
                        if val == 'memory[%s:%s+32], %s' % (address, address, memory):
                            var_name = key
                            mem_var_exist = True
                            break

                    if mem_var_exist:
                        value = BitVec(var_name, 256)
                        gas_constraint = add_gas_constraint(value, UNSIGNED_BOUND_NUMBER)
                    else:
                        new_var_name = get_gen().gen_mem_var(line)
                        value = BitVec(new_var_name, 256)
                        gas_constraint = add_gas_constraint(value, UNSIGNED_BOUND_NUMBER)

                        if not var_in_var_table(new_var_name):
                            add_var_table(new_var_name, 'memory[%s:%s+32], %s' % (address, address, memory))

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
                    # NOTE: Check if sym var is already created or not
                    sto_var_exist = False
                    var_name = None
                    for key, val in get_var_table().items():
                        if val == 'storage[%s]' % address:
                            var_name = key
                            sto_var_exist = True
                            break

                    if sto_var_exist:
                        value = BitVec(var_name, 256)
                        gas_constraint = add_gas_constraint(value, UNSIGNED_BOUND_NUMBER)
                    else:
                        new_var_name = get_gen().gen_owner_store_var(line)
                        value = BitVec(new_var_name, 256)
                        gas_constraint = add_gas_constraint(value, UNSIGNED_BOUND_NUMBER)

                        if not var_in_var_table(new_var_name):
                            add_var_table(new_var_name, 'storage[%s], %s' % (address, storage))
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

            if len(storage) == 0:
                if isinstance(value, int):
                    if value == 0:
                        gas = 5000
                    else:
                        gas = 20000
                else:
                    gas = simplify(BV2Int(If(Not(value == 0), BitVecVal(20000, 256), BitVecVal(5000, 256))))
            else:
                if isinstance(address, int) and all([isinstance(e, int) for e in storage.keys()]):
                    if address in storage.keys():
                        gas = 5000
                    else:
                        if value == 0:
                            gas = 5000
                        else:
                            gas = 20000
                else:
                    cond = False
                    for k in [e for e in storage.keys() if is_expr(e)]:
                        cond = Or(cond, k == address)
                    gas = simplify(BV2Int(If(Or(Not(value == 0), cond), BitVecVal(5000, 256), BitVecVal(20000, 256))))
            storage[str(address)] = value

        else:
            raise ValueError('STACK underflow')
    elif opcode == 'JUMP':
        # if not (len(instruction_set) > 1 and instruction_set[1] == '[out]'):
        if len(stack) > 0:
            row = len(stack) - 1
            next_tag = stack.pop(str(row))

            # NOTE: GAS
            gas = gas_table[opcode]
        else:
            raise ValueError('STACK underflow')
    elif opcode == 'JUMPI':
        if len(stack) > 1:
            row = len(stack) - 1
            next_tag = stack.pop(str(row))
            constraint = stack.pop(str(row - 1))

            # NOTE: Path Constraint
            path_constraint = constraint

            # NOTE: GAS
            gas = gas_table[opcode]
        else:
            raise ValueError('STACK underflow')
    elif opcode == 'GAS':
        new_var_name = get_gen().gen_gas_var(line)
        new_var = BitVec(new_var_name, 256)
        gas_constraint = add_gas_constraint(new_var, UNSIGNED_BOUND_NUMBER)

        if not var_in_var_table(new_var_name):
            add_var_table(new_var_name, 'Gas Remaining')

        row = len(stack)
        stack[str(row)] = new_var

        # NOTE: GAS
        gas = gas_table[opcode]
    elif opcode.startswith('PUSH', 0):
        # NOTE: this is a push instruction
        if len(instruction_set) > 1:
            if instruction_set[1] == '[tag]':
                pushed_value = int(instruction_set[2])
            elif instruction_set[1] == 'data':
                pushed_value = int(str(instruction_set[2]), 16)
            else:
                pushed_value = int(str(instruction_set[1]), 16)
        else:
            if instruction_set[0] == 'PUSHDEPLOYADDRESS':
                new_var_name = get_gen().gen_arbitrary_address_var(line)
                pushed_value = BitVec(new_var_name, 256)
                gas_constraint = add_gas_constraint(pushed_value, UNSIGNED_BOUND_NUMBER)

                if not var_in_var_table(new_var_name):
                    add_var_table(new_var_name, 'address(deployed)')
            else:
                raise ValueError('PUSH ERROR')
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
            # return None, None, None, None, None
            raise ValueError('STACK underflow')
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
            row = len(stack) - 1
            offset = stack.pop(str(row))
            word = stack.pop(str(row-1))
            for _ in range(int(opcode[3:])):
                num_of_pops -= 1
                row = len(stack) - 1
                pop_value = stack.pop(str(row))

            # NOTE: GAS
            if isinstance(word, int):
                gas = (int(opcode[3:]) + 1) * 375 + (8 * (len(hex(word)) - 2))
            else:
                new_var_name = get_gen().gen_sha_word_size(str(word).split('_')[1])
                new_var = BitVec(new_var_name, 256)
                gas = (int(opcode[3:]) + 1) * 375 + (8 * BV2Int(new_var))
                gas_constraint = add_gas_constraint(new_var, BYTE_BOUND_NUMBER)

                if not var_in_var_table(new_var_name):
                    add_var_table(new_var_name, 'The bytes of %s' % word)
        else:
            raise ValueError('STACK underflow')
    elif opcode == 'CALL':
        if len(stack) > 6:
            row = len(stack) - 1
            out_gas = stack.pop(str(row))
            addr = stack.pop(str(row - 1))
            out_value = stack.pop(str(row - 2))
            in_position = stack.pop(str(row - 3))
            in_length = stack.pop(str(row - 4))
            out_position = stack.pop(str(row - 5))
            out_length = stack.pop(str(row - 6))

            row = len(stack)
            new_var_name = get_gen().gen_call_success(line)
            new_var = BitVec(new_var_name, 256)
            stack[str(row)] = new_var
            gas_constraint = Or(new_var == 1, new_var == 0)

            # NOTE: GAS
            # TODO: handle gas
            gas = gas_table[opcode]
            out_value = out_value.as_long() if isinstance(out_value, z3.z3.BitVecNumRef) else out_value
            if isinstance(out_value, int) and out_value != 0:
                gas += 9000
            elif is_expr(out_value):
                g = If(out_value == 0, 0, 9000)
                if is_bv(g):
                    gas += BV2Int(If(out_value == 0, 0, 9000))
                else:
                    gas += If(out_value == 0, 0, 9000)
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

            row = len(stack)
            new_var_name = get_gen().gen_call_success(line)
            new_var = BitVec(new_var_name, 256)
            stack[str(row)] = new_var
            gas_constraint = Or(new_var == 1, new_var == 0)

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
            gas_constraint = add_gas_constraint(new_var, UNSIGNED_BOUND_NUMBER)

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
            gas_constraint = add_gas_constraint(new_var, UNSIGNED_BOUND_NUMBER)

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
            gas_constraint = add_gas_constraint(new_var, UNSIGNED_BOUND_NUMBER)

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
            gas_constraint = add_gas_constraint(new_var, UNSIGNED_BOUND_NUMBER)
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
            gas = 5000 + BV2Int(If(new_var, 25000, 0))
        else:
            raise ValueError('STACK underflow')
    else:
        raise Exception('UNKNOWN INSTRUCTION:', opcode)

    if isinstance(gas, float):
        gas = int(round(gas))

    return state, gas, path_constraint, gas_constraint, var_constraint, prev_jumpi_ins, str(next_tag)