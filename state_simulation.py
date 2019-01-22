import six
import sha3
from z3 import *
from gas_price import gas_table

UNSIGNED_BOUND_NUMBER = 2**256 - 1


def state_simulation(instruction, state):
    global solver

    stack = state[0]
    memory = state[1]
    storage = state[2]
    instruction_set = instruction.split(' ')
    opcode = instruction_set[0]
    gas = 0

    if opcode in ['INVALID', 'STOP', 'REVERT', 'JUMPDEST']:
        pass
    elif opcode == 'TIMESTAMP':
        row = len(stack)
        stack[row] = 'TIMESTAMP'

        # NOTE: GAS
        gas = gas_table[opcode]
    elif opcode == 'ADD':
        if len(stack) > 1:
            row = len(stack) - 1
            first = stack.pop(row)
            second = stack.pop(row - 1)

            if isinstance(first, int) and isinstance(second, int):
                computed = first + second
            else:
                computed = '(' + str(first) + '+' + str(second) + ')'

            row = len(stack)
            stack[row] = computed

            # NOTE: GAS
            gas = gas_table[opcode]
        else:
            raise ValueError('STACK underflow')
    elif opcode == 'MUL':
        if len(stack) > 1:
            row = len(stack) - 1
            first = stack.pop(row)
            second = stack.pop(row - 1)

            if isinstance(first, int) and isinstance(second, int):
                computed = first * second & UNSIGNED_BOUND_NUMBER
            else:
                computed = '(' + str(first) + '*' + str(second) + ')'

            row = len(stack)
            stack[row] = computed

            # NOTE: GAS
            gas = gas_table[opcode]
        else:
            raise ValueError('STACK underflow')
    elif opcode == 'SUB':
        if len(stack) > 1:
            row = len(stack) - 1
            first = stack.pop(row)
            second = stack.pop(row - 1)

            if isinstance(first, int) and isinstance(second, int):
                computed = first - second
            else:
                computed = '(' + str(first) + '-' + str(second) + ')'

            row = len(stack)
            stack[row] = computed

            # NOTE: GAS
            gas = gas_table[opcode]
        else:
            raise ValueError('STACK underflow')
    elif opcode == 'DIV':
        if len(stack) > 1:
            row = len(stack) - 1
            first = stack.pop(row)
            second = stack.pop(row - 1)

            if isinstance(first, int) and isinstance(second, int):
                if second == 0:
                    computed = 0
                else:
                    first = to_unsigned(first)
                    second = to_unsigned(second)
                    computed = int(first / second)
            else:
                computed = '(' + str(first) + '/' + str(second) + ')'

            row = len(stack)
            stack[row] = computed

            # NOTE: GAS
            gas = gas_table[opcode]
        else:
            raise ValueError('STACK underflow')
    elif opcode == 'SDIV':
        if len(stack) > 1:
            row = len(stack) - 1
            first = stack.pop(row)
            second = stack.pop(row - 1)

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
                    solver.add( Not( And(first == -2**255, second == -1 ) ))
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
            stack[row] = computed

            # NOTE: GAS
            gas = gas_table[opcode]
        else:
            raise ValueError('STACK underflow')
    elif opcode == 'MOD':
        if len(stack) > 1:
            row = len(stack) - 1
            first = stack.pop(row)
            second = stack.pop(row - 1)

            if isinstance(first, int) and isinstance(second, int):
                if second == 0:
                    computed = 0
                else:
                    first = to_unsigned(first)
                    second = to_unsigned(second)
                    computed = first % second & UNSIGNED_BOUND_NUMBER
            else:
                computed = '(' + str(first) + '%' + str(second) + ')'

            row = len(stack)
            stack[row] = computed

            # NOTE: GAS
            gas = gas_table[opcode]
        else:
            raise ValueError('STACK underflow')
    elif opcode == 'SMOD':
        if len(stack) > 1:
            row = len(stack) - 1
            first = stack.pop(row)
            second = stack.pop(row - 1)

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
            stack[row] = computed

            # NOTE: GAS
            gas = gas_table[opcode]
        else:
            raise ValueError('STACK underflow')
    elif opcode == 'ADDMOD':
        if len(stack) > 2:
            row = len(stack) - 1
            first = stack.pop(row)
            second = stack.pop(row - 1)
            third = stack.pop(row - 2)

            if is_all_real(first, second, third):
                if third == 0:
                    computed = 0
                else:
                    computed = (first + second) % third
            else:
                first = to_symbolic(first)
                second = to_symbolic(second)
                solver.push()
                solver.add(Not(third == 0))
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
            first = stack.pop(row)
            second = stack.pop(row - 1)
            third = stack.pop(row - 2)

            if is_all_real(first, second, third):
                if third == 0:
                    computed = 0
                else:
                    computed = (first * second) % third
            else:
                first = to_symbolic(first)
                second = to_symbolic(second)
                solver.push()
                solver.add(Not(third == 0))
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
            stack[row] = computed

            # NOTE: GAS
            gas = gas_table[opcode]
        else:
            raise ValueError('STACK underflow')
    elif opcode == 'EXP':
        if len(stack) > 1:
            row = len(stack) - 1
            base = stack.pop(row)
            exponent = stack.pop(row - 1)

            computed = 0
            if is_all_real(base, exponent):
                computed = pow(base, exponent, 2 ** 256)
                row = len(stack)
                stack[row] = computed

                # NOTE: GAS
                if computed == 0:
                    gas = 10
                else:
                    gas = 10 + (10 * (1 + math.log(computed, 256)))
            else:
                if isinstance(base, str):
                    computed = '(' + base + '/' + str(exponent) + ')'
                elif isinstance(exponent, str):
                    computed = '(' + str(base) + '**' + exponent + ')'

                row = len(stack)
                stack[row] = computed

                # NOTE: GAS
                gas = '10+(10*(1+log256(%s)))' % computed
        else:
            raise ValueError('STACK underflow')
    elif opcode == 'SIGNEXTEND':
        if len(stack) > 1:
            row = len(stack) - 1
            first = stack.pop(row)
            second = stack.pop(row - 1)

            if is_all_real(first, second):
                if first >= 32 or first < 0:
                    computed = second
                else:
                    signbit_index_from_right = 8 * first + 7
                    if second & (1 << signbit_index_from_right):
                        computed = second | (2 ** 256 - (1 << signbit_index_from_right))
                    else:
                        computed = second & ((1 << signbit_index_from_right) - 1)
            else:
                first = to_symbolic(first)
                second = to_symbolic(second)
                solver.push()
                solver.add(Not(Or(first >= 32, first < 0)))
                if check_sat(solver) == unsat:
                    computed = second
                else:
                    signbit_index_from_right = 8 * first + 7
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
            first = stack.pop(row)
            second = stack.pop(row - 1)

            if isinstance(first, int) and isinstance(second, int):
                first = to_unsigned(first)
                second = to_unsigned(second)
                if first < second:
                    computed = 1
                else:
                    computed = 0
            else:
                if isinstance(first, int) and isinstance(second, int):
                    first = to_unsigned(first)
                    second = to_unsigned(second)
                    if first < second:
                        computed = 1
                    else:
                        computed = 0
                else:
                    computed = '(' + str(first) + '<' + str(second) + ')'

            row = len(stack)
            stack[row] = computed

            # NOTE: GAS
            gas = gas_table[opcode]
        else:
            raise ValueError('STACK underflow')
    elif opcode == 'GT':
        if len(stack) > 1:
            row = len(stack) - 1
            first = stack.pop(row)
            second = stack.pop(row - 1)

            if isinstance(first, int) and isinstance(second, int):
                first = to_unsigned(first)
                second = to_unsigned(second)
                if first > second:
                    computed = 1
                else:
                    computed = 0
            else:
                if isinstance(first, int) and isinstance(second, int):
                    first = to_unsigned(first)
                    second = to_unsigned(second)
                    if first > second:
                        computed = 1
                    else:
                        computed = 0
                else:
                    computed = '(' + str(first) + '>' + str(second) + ')'

            row = len(stack)
            stack[row] = computed

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

            if isinstance(first, int) and isinstance(second, int):
                first = to_signed(first)
                second = to_signed(second)
                if first < second:
                    computed = 1
                else:
                    computed = 0
            else:
                computed = '(' + str(first) + '<' + str(second) + ')'

            row = len(stack)
            stack[row] = computed

            # NOTE: GAS
            gas = gas_table[opcode]
        else:
            raise ValueError('STACK underflow')
    elif opcode == 'SGT':
        # FIXME: Not fully faithful to signed comparison
        if len(stack) > 1:
            row = len(stack) - 1
            first = stack.pop(row)
            second = stack.pop(row - 1)

            if isinstance(first, int) and isinstance(second, int):
                first = to_signed(first)
                second = to_signed(second)
                if first > second:
                    computed = 1
                else:
                    computed = 0
            else:
                computed = '(' + str(first) + '>' + str(second) + ')'

            row = len(stack)
            stack[row] = computed

            # NOTE: GAS
            gas = gas_table[opcode]
        else:
            raise ValueError('STACK underflow')
    elif opcode == 'EQ':
        if len(stack) > 1:
            row = len(stack) - 1
            first = stack.pop(row)
            second = stack.pop(row - 1)

            if isinstance(first, int) and isinstance(second, int):
                if first == second:
                    computed = 1
                else:
                    computed = 0
            else:
                if isinstance(first, str):
                    computed = '(' + str(first) + '=' + str(second) + ')'
                elif isinstance(second, str):
                    computed = '(' + str(first) + '=' + str(second) + ')'
                else:
                    if first == second:
                        computed = 1
                    else:
                        computed = 0

            row = len(stack)
            stack[row] = computed

            # NOTE: GAS
            gas = gas_table[opcode]
        else:
            raise ValueError('STACK underflow')
    elif opcode == 'ISZERO':
        if len(stack) > 0:
            row = len(stack) - 1
            first = stack.pop(row)

            if isinstance(first, int):
                if first == 0:
                    computed = 1
                else:
                    computed = 0
            else:
                if isinstance(first, int):
                    if first == 0:
                        computed = 1
                    else:
                        computed = 0
                else:
                    computed = '(' + str(first) + '==0' + ')'

            row = len(stack)
            stack[row] = computed

            # NOTE: GAS
            gas = gas_table[opcode]
        else:
            raise ValueError('STACK underflow')
    elif opcode == 'AND':
        if len(stack) > 1:
            row = len(stack) - 1
            first = stack.pop(row)
            second = stack.pop(row - 1)

            if isinstance(first, int) and isinstance(second, int):
                computed = int(first) & second
            else:
                computed = '(' + str(first) + '&' + str(second) + ')'

            row = len(stack)
            stack[row] = computed

            # NOTE: GAS
            gas = gas_table[opcode]
        else:
            raise ValueError('STACK underflow')
    elif opcode == 'OR':
        if len(stack) > 1:
            row = len(stack) - 1
            first = stack.pop(row)
            second = stack.pop(row - 1)

            if isinstance(first, int) and isinstance(second, int):
                computed = first | second
            else:
                computed = '(' + str(first) + '|' + str(second) + ')'

            row = len(stack)
            stack[row] = computed

            # NOTE: GAS
            gas = gas_table[opcode]
        else:
            raise ValueError('STACK underflow')
    elif opcode == 'XOR':
        if len(stack) > 1:
            row = len(stack) - 1
            first = stack.pop(row)
            second = stack.pop(row - 1)

            if isinstance(first, int) and isinstance(second, int):
                computed = first ^ second
            else:
                computed = str(first) + '^' + str(second)

            row = len(stack)
            stack[row] = computed

            # NOTE: GAS
            gas = gas_table[opcode]
        else:
            raise ValueError('STACK underflow')
    elif opcode == 'NOT':
        if len(stack) > 0:
            row = len(stack) - 1
            first = stack.pop(row)

            if isinstance(first, int):
                computed = (~first) & UNSIGNED_BOUND_NUMBER
            else:
                computed = '(' + '~' + str(first) + ')'

            row = len(stack)
            stack[row] = computed

            # NOTE: GAS
            gas = gas_table[opcode]
        else:
            raise ValueError('STACK underflow')
    elif opcode == 'BYTE':
        if len(stack) > 1:
            row = len(stack) - 1
            first = stack.pop(row)
            second = stack.pop(row - 1)
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
            stack[row] = computed

            # NOTE: GAS
            gas = gas_table[opcode]
        else:
            raise ValueError('STACK underflow')
    elif opcode in ['SHA3', 'KECCAK256']:
        if len(stack) > 1:
            row = len(stack) - 1
            # print('[ROW]:', row, row - 1, stack)
            position = stack.pop(row)
            to = stack.pop(row - 1)
            # print('[TO]:', position, to)

            # FIXME: NEED TO CHECK INT OR NOT
            try:
                data = str(memory[str(position)])
                computed = sha3.sha3_224(data.encode('utf-8')).hexdigest()
            except KeyError:
                data = 'memory[%s:%s]' % (str(position), str(to))
                computed = 'SHA3(%s)' % data

            row = len(stack)
            stack[row] = computed

            # NOTE: GAS
            if isinstance(data, int):
                gas = 30 + 6 * data
            else:
                gas = '30+6*%s' % str(data)
        else:
            raise ValueError('STACK underflow')
    elif opcode == 'ADDRESS':
        # NOTE: get address of currently executing account
        # TODO: handle it
        row = len(stack)
        stack[row] = 'CurrentAddress'

        # NOTE: GAS
        gas = gas_table[opcode]
    elif opcode == 'BALANCE':
        # TODO: handle it
        if len(stack) > 0:
            row = len(stack) - 1
            address = stack.pop(row)

            row = len(stack)
            stack[row] = 'BalanceOf%s' % str(address)

            # NOTE: GAS
            gas = gas_table[opcode]
        else:
            raise ValueError('STACK underflow')
    elif opcode == 'CALLER':
        # NOTE: get caller address
        # TODO: handle it
        row = len(stack)
        stack[row] = 'CallerAddress'

        # NOTE: GAS
        gas = gas_table[opcode]
    elif opcode == 'CALLVALUE':
        # NOTE: get value of this transaction
        # TODO: handle it
        row = len(stack)
        stack[row] = 'DepositedValue'

        # NOTE: GAS
        gas = gas_table[opcode]
    elif opcode == 'CALLDATALOAD':
        # NOTE: from input data from environment
        # TODO: handle it
        if len(stack) > 0:
            row = len(stack) - 1
            position = stack.pop(row)

            row = len(stack)
            stack[row] = 'DataAt%s' % str(position)

            # NOTE: GAS
            gas = gas_table[opcode]
        else:
            raise ValueError('STACK underflow')
    elif opcode == 'CALLDATASIZE':
        # TODO: handle it
        row = len(stack)
        stack[row] = 'InputDataSize'

        # NOTE: GAS
        gas = gas_table[opcode]
    elif opcode == "CALLDATACOPY":
        # NOTE: Copy input data to memory
        if len(stack) > 2:
            row = len(stack) - 1
            memory_position = stack.pop(row)
            data_position = stack.pop(row - 1)
            num_bytes = stack.pop(row - 2)

            # TODO: handle gas and memory
            # NOTE: GAS
            gas = '2+3*InputWordsNumber'
        else:
            raise ValueError('STACK underflow')
    elif opcode == 'CODESIZE':
        # TODO: handle it
        row = len(stack)
        stack[row] = 'CurrentCodeSize'

        # NOTE: GAS
        gas = gas_table[opcode]
    elif opcode == 'CODECOPY':
        if len(stack) > 2:
            row = len(stack) - 1
            memory_position = stack.pop(row)
            code_position = stack.pop(row - 1)
            num_bytes = stack.pop(row - 2)

            # TODO: handle gas and memory
            # NOTE: GAS
            gas = '2+3*CodeWordsNumber'
        else:
            raise ValueError('STACK underflow')
    elif opcode == 'GASPRICE':
        # TODO: handle it
        row = len(stack)
        stack[row] = 'CurrentGasPrice'

        # NOTE: GAS
        gas = gas_table[opcode]
    elif opcode == 'RETURNDATACOPY':
        if len(stack) > 2:
            row = len(stack) - 1
            z = stack.pop(row)
            y = stack.pop(row - 1)
            x = stack.pop(row - 2)

            # TODO: handle gas and memory
            # NOTE: GAS
            gas = '2+3*InputWordsNumber'
        else:
            raise ValueError('STACK underflow')
    elif opcode == 'RETURNDATASIZE':
        # TODO: handle it
        row = len(stack)
        stack[row] = 'size(returndata)'

        # NOTE: GAS
        gas = gas_table[opcode]
    elif opcode == 'NUMBER':
        # NOTE: information from block header
        # TODO: handle it
        row = len(stack)
        stack[row] = 'currentNumber'

        # NOTE: GAS
        gas = gas_table[opcode]
    elif opcode == 'POP':
        if len(stack) > 0:
            row = len(stack) - 1
            stack.pop(row)

            # NOTE: GAS
            gas = gas_table[opcode]
        else:
            raise ValueError('STACK underflow')
    elif opcode == 'MLOAD':
        if len(stack) > 0:
            row = len(stack) - 1
            address = stack.pop(row)

            value = ''
            for key, val in memory.items():
                if address == key:
                    value = val

            if value == '':
                if is_real(address):
                    value = 'memory[%s:%s]' % (str(address), str(address + 32))
                else:
                    value = 'memory[%s:%s]' % (str(address), str(address) + '+32')

            row = len(stack)
            stack[row] = value

            # NOTE: GAS
            gas = gas_table[opcode]
        else:
            raise ValueError('STACK underflow')
    elif opcode == 'MSTORE':
        if len(stack) > 1:
            row = len(stack) - 1
            address = stack.pop(row)
            value = stack.pop(row - 1)
            memory[str(address)] = value

            # NOTE: GAS
            gas = gas_table[opcode]
        else:
            raise ValueError('STACK underflow')
    elif opcode == 'SLOAD':
        if len(stack) > 0:
            row = len(stack) - 1
            address = stack.pop(row)

            value = ''
            for key, val in storage.items():
                if key == address:
                    value = val
            row = len(stack)
            stack[row] = value

            # NOTE: GAS
            gas = gas_table[opcode]
        else:
            raise ValueError('STACK underflow')
    elif opcode == 'SSTORE':
        if len(stack) > 1:
            row = len(stack) - 1
            address = stack.pop(row)
            value = stack.pop(row - 1)
            storage[str(address)] = value

            if is_all_real(address, value):
                if address == 0 and value != 0:
                    gas = 20000
                else:
                    gas = 5000
            else:
                gas = '((%s != 0) && (%s == 0)) ? 20000 : 5000' % (str(value), str(address))

        else:
            raise ValueError('STACK underflow')
    elif opcode == 'JUMP':
        if len(stack) > 0:
            row = len(stack) - 1
            stack.pop(row)

            # NOTE: GAS
            gas = gas_table[opcode]
        else:
            raise ValueError('STACK underflow')
    elif opcode == 'JUMPI':
        if len(stack) > 1:
            row = len(stack) - 1
            address = stack.pop(row)
            constraint = stack.pop(row - 1)

            # NOTE: GAS
            gas = gas_table[opcode]

            # TODO: handle path constraint
        else:
            raise ValueError('STACK underflow')
    elif opcode == 'GAS':
        row = len(stack)
        stack[row] = 'GasAvailable'

        # NOTE: GAS
        gas = gas_table[opcode]
    elif opcode.startswith('PUSH', 0):
        # NOTE: this is a push instruction
        pushed_value = ''
        if instruction_set[1] == '[tag]':
            pushed_value = int(instruction_set[2])
        else:
            try:
                pushed_value = int(instruction_set[1])
            except ValueError:
                if len(instruction_set[1]) > 4:
                    pushed_value = str(instruction_set[1])
                elif instruction_set[1] == 'data':
                    if len(instruction_set[1]) > 4:
                        pushed_value = str(instruction_set[2])
                else:
                    pushed_value = int(instruction_set[1], 16)
        row = len(stack)
        stack[row] = pushed_value

        # NOTE: GAS
        gas = gas_table['PUSH']
    elif opcode.startswith('DUP', 0):
        position = int(opcode[3:], 10) - 1
        if len(stack) > position:
            duplicate_value = stack[position]
            row = len(stack)
            stack[row] = duplicate_value

            # NOTE: GAS
            gas = gas_table['DUP']
        else:
            raise ValueError('STACK underflow')
    elif opcode.startswith('SWAP', 0):
        position = int(opcode[4:], 10)
        if len(stack) > position:
            temp_value = stack[position]
            row = len(stack) - 1
            stack[position] = stack[row]
            stack[row] = temp_value

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
                pop_value = stack.pop(row)

                # NOTE: GAS
                if count == 1:
                    if isinstance(pop_value, str):
                        gas = '%s+(8*%s)' % (str((int(opcode[3:]) + 1) * 375), pop_value)
                    else:
                        gas = (int(opcode[3:]) + 1) * 375 + (8 * pop_value)
        else:
            raise ValueError('STACK underflow')
    elif opcode == 'CALL':
        # TODO: Need to handle miu_i
        if len(stack) > 6:
            row = len(stack) - 1
            out_gas = stack.pop(row)
            recipient = stack.pop(row - 1)
            out_wei = stack.pop(row - 2)
            in_value = stack.pop(row - 3)
            in_size = stack.pop(row - 4)
            out_value = stack.pop(row - 5)
            out_size = stack.pop(row - 6)

            row = len(stack)
            stack[row] = 'CallReturn'

            # NOTE: GAS
            # TODO: handle gas
            gas = gas_table[opcode]
        else:
            raise ValueError('STACK underflow')
    elif opcode == 'CALLCODE':
        if len(stack) > 6:
            row = len(stack) - 1
            out_gas = stack.pop(row)
            recipient = stack.pop(row - 1)
            out_wei = stack.pop(row - 2)
            in_value = stack.pop(row - 3)
            in_size = stack.pop(row - 4)
            out_value = stack.pop(row - 5)
            out_size = stack.pop(row - 6)

            row = len(stack)
            stack[row] = 'CallCodeReturn'

            # NOTE: GAS
            # TODO: handle gas
            gas = gas_table[opcode]
        else:
            raise ValueError('STACK underflow')
    elif opcode in ['DELEGATECALL', 'STATICCALL']:
        if len(stack) > 2:
            row = len(stack) - 1
            out_gas = stack.pop(row)
            recipient = stack.pop(row - 1)
            in_value = stack.pop(row - 2)
            in_size = stack.pop(row - 3)
            out_value = stack.pop(row - 4)
            out_size = stack.pop(row - 5)

            row = len(stack)
            stack[row] = 'DelegateCallStaticCallReturn'

            # NOTE: GAS
            # TODO: handle gas
            gas = gas_table[opcode]
        else:
            raise ValueError('STACK underflow')
    elif opcode == 'RETURN':
        # TODO: Need to handle miu_i
        if len(stack) > 1:
            row = len(stack) - 1
            stack.pop(row)
            stack.pop(row - 1)

            # NOTE: GAS
            gas = gas_table[opcode]
        else:
            raise ValueError('STACK underflow')
    elif opcode == 'CREATE':
        if len(stack) > 2:
            row = len(stack) - 1
            wei = stack.pop(row)
            position = stack.pop(row - 1)
            length = stack.pop(row - 2)

            row = len(stack)
            stack[row] = 'NewAddress'

            # NOTE: GAS
            gas = gas_table[opcode]
        else:
            raise ValueError('STACK underflow')
    elif opcode == 'EXTCODESIZE':
        if len(stack) > 0:
            row = len(stack) - 1
            address = stack.pop(row)

            row = len(stack)
            stack[row] = 'CodeAt%s' % str(address)

            # NOTE: GAS
            gas = gas_table[opcode]
        else:
            raise ValueError('STACK underflow')
    else:
        raise Exception('UNKNOWN INSTRUCTION:', opcode)

    if isinstance(gas, float):
        gas = int(round(gas))
    return state, gas


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