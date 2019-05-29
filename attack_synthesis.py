import sha3
from global_vars import *
from global_constants import *
from z3_func import *
from gas_price import gas_table

model = None


def attack_synthesis(path, nodes, m):
    global  model

    model = m
    state = {'Stack': {}, 'Memory': {}, 'Storage': {}}
    gas = 0

    for addr in path:
        for node in nodes:
            if node['addr'] == addr:
                ins_list = node['ins']

                for ins in ins_list:
                    ins_set = ins.split(': ')
                    line = ins_set[0]
                    opcode = ins_set[1]

                    if opcode.split(' ')[0] == 'tag':
                        pass
                    elif line == 'Stack Sum':
                        break
                    else:
                        state, ins_gas = ins_sim(state, opcode, line)
                        gas += ins_gas

                        if opcode in \
                                ['STOP', 'RETURN', 'REVERT', 'INVALID', 'JUMP', 'JUMP [in]', 'JUMP [out]', 'JUMPI']:
                            break
                break
    print('[INFO] Attack Synthesis Gas:', gas)
    return int(gas)


def ins_sim(state, instruction, line):
    global model

    stack = state['Stack']
    memory = state['Memory']
    storage = state['Storage']
    instruction_set = instruction.split(' ')
    opcode = instruction_set[0]
    gas = 0

    for key, val in stack.items():
        if isinstance(val, z3.z3.BitVecNumRef):
            stack[key] = val.as_long()

    if opcode in ['INVALID', 'STOP', 'REVERT', 'JUMPDEST']:
        pass
    elif opcode == 'TIMESTAMP':
        var = get_gen().gen_time_var(line)
        val = get_model_var(var)

        row = len(stack)
        stack[str(row)] = val

        # NOTE: GAS
        gas = gas_table[opcode]
    elif opcode == 'ADD':
        row = len(stack) - 1
        first = stack.pop(str(row))
        second = stack.pop(str(row - 1))

        row = len(stack)
        stack[str(row)] = first + second

        # NOTE: GAS
        gas = gas_table[opcode]
    elif opcode == 'MUL':
        row = len(stack) - 1
        first = stack.pop(str(row))
        second = stack.pop(str(row - 1))

        row = len(stack)
        stack[str(row)] = first * second

        # NOTE: GAS
        gas = gas_table[opcode]
    elif opcode == 'SUB':
        row = len(stack) - 1
        first = stack.pop(str(row))
        second = stack.pop(str(row - 1))

        row = len(stack)
        stack[str(row)] = (first - second) % (2 ** 256)

        # NOTE: GAS
        gas = gas_table[opcode]
    elif opcode == 'DIV':
        row = len(stack) - 1
        first = stack.pop(str(row))
        second = stack.pop(str(row - 1))

        if second == 0:
            computed = 0
        else:
            first = to_unsigned(first)
            second = to_unsigned(second)
            computed = first // second
        row = len(stack)
        stack[str(row)] = computed

        # NOTE: GAS
        gas = gas_table[opcode]
    elif opcode == 'SDIV':
        row = len(stack) - 1
        first = stack.pop(str(row))
        second = stack.pop(str(row - 1))

        first = to_signed(first)
        second = to_signed(second)
        if second == 0:
            computed = 0
        elif first == -2 ** 255 and second == -1:
            computed = -2 ** 255
        else:
            sign = -1 if (first / second) < 0 else 1
            computed = sign * (abs(first) / abs(second))

        row = len(stack)
        stack[str(row)] = computed

        # NOTE: GAS
        gas = gas_table[opcode]
    elif opcode == 'MOD':
        row = len(stack) - 1
        first = stack.pop(str(row))
        second = stack.pop(str(row - 1))

        if second == 0:
            computed = 0
        else:
            first = to_unsigned(first)
            second = to_unsigned(second)
            computed = first % second & UNSIGNED_BOUND_NUMBER

        row = len(stack)
        stack[str(row)] = computed

        # NOTE: GAS
        gas = gas_table[opcode]
    elif opcode == 'SMOD':
        row = len(stack) - 1
        first = stack.pop(str(row))
        second = stack.pop(str(row - 1))

        if second == 0:
            computed = 0
        else:
            first = to_signed(first)
            second = to_signed(second)
            sign = -1 if first < 0 else 1
            computed = sign * (abs(first) % abs(second))

        row = len(stack)
        stack[str(row)] = computed

        # NOTE: GAS
        gas = gas_table[opcode]
    elif opcode == 'ADDMOD':
        row = len(stack) - 1
        first = stack.pop(str(row))
        second = stack.pop(str(row - 1))
        third = stack.pop(str(row - 2))

        if third == 0:
            computed = 0
        else:
            computed = (first + second) % third

        row = len(stack)
        stack[row] = computed

        # NOTE: GAS
        gas = gas_table[opcode]
    elif opcode == 'MULMOD':
        row = len(stack) - 1
        first = stack.pop(str(row))
        second = stack.pop(str(row - 1))
        third = stack.pop(str(row - 2))

        if third == 0:
            computed = 0
        else:
            computed = (first * second) % third

        row = len(stack)
        stack[str(row)] = computed

        # NOTE: GAS
        gas = gas_table[opcode]
    elif opcode == 'EXP':
        row = len(stack) - 1
        base = stack.pop(str(row))
        exponent = stack.pop(str(row - 1))

        computed = pow(base, exponent, 2 ** 256)

        row = len(stack)
        stack[str(row)] = computed

        # NOTE: GAS
        if computed == 0:
            gas = 10
        else:
            gas = 10 + 10 * (1 + math.log(computed, 256))
    elif opcode == 'SIGNEXTEND':
        row = len(stack) - 1
        bit = stack.pop(str(row))
        second = stack.pop(str(row - 1))

        if bit >= 32 or bit < 0:
            computed = second
        else:
            signbit_index_from_right = 8 * bit + 7
            if second & (1 << signbit_index_from_right):
                computed = second | (2 ** 256 - (1 << signbit_index_from_right))
            else:
                computed = second & ((1 << signbit_index_from_right) - 1)

        row = len(stack)
        stack[row] = computed

        # NOTE: GAS
        gas = gas_table[opcode]
    elif opcode == 'LT':
        row = len(stack) - 1
        first = stack.pop(str(row))
        second = stack.pop(str(row - 1))

        first = to_unsigned(first)
        second = to_unsigned(second)
        if first < second:
            computed = 1
        else:
            computed = 0

        row = len(stack)
        stack[str(row)] = computed

        # NOTE: GAS
        gas = gas_table[opcode]
    elif opcode == 'GT':
        row = len(stack) - 1
        first = stack.pop(str(row))
        second = stack.pop(str(row - 1))

        first = to_unsigned(first)
        second = to_unsigned(second)
        if first > second:
            computed = 1
        else:
            computed = 0

        row = len(stack)
        stack[str(row)] = computed

        # NOTE: GAS
        gas = gas_table[opcode]
    elif opcode == 'SLT':
        row = len(stack) - 1
        first = stack.pop(row)
        second = stack.pop(row - 1)

        first = to_signed(first)
        second = to_signed(second)
        if first < second:
            computed = 1
        else:
            computed = 0

        row = len(stack)
        stack[str(row)] = computed

        # NOTE: GAS
        gas = gas_table[opcode]
    elif opcode == 'SGT':
        row = len(stack) - 1
        first = stack.pop(str(row))
        second = stack.pop(str(row - 1))

        first = to_signed(first)
        second = to_signed(second)
        if first > second:
            computed = 1
        else:
            computed = 0

        row = len(stack)
        stack[str(row)] = computed

        # NOTE: GAS
        gas = gas_table[opcode]
    elif opcode == 'EQ':
        row = len(stack) - 1
        first = stack.pop(str(row))
        second = stack.pop(str(row - 1))

        if first == second:
            computed = 1
        else:
            computed = 0

        row = len(stack)
        stack[str(row)] = computed

        # NOTE: GAS
        gas = gas_table[opcode]
    elif opcode == 'ISZERO':
        row = len(stack) - 1
        first = stack.pop(str(row))

        if first == 0:
            computed = 1
        else:
            computed = 0

        row = len(stack)
        stack[str(row)] = computed

        # NOTE: GAS
        gas = gas_table[opcode]
    elif opcode == 'AND':
        row = len(stack) - 1
        first = stack.pop(str(row))
        second = stack.pop(str(row - 1))

        row = len(stack)
        stack[str(row)] = first & second

        # NOTE: GAS
        gas = gas_table[opcode]
    elif opcode == 'OR':
        row = len(stack) - 1
        first = stack.pop(str(row))
        second = stack.pop(str(row - 1))

        row = len(stack)
        stack[str(row)] = first | second

        # NOTE: GAS
        gas = gas_table[opcode]
    elif opcode == 'XOR':
        row = len(stack) - 1
        first = stack.pop(str(row))
        second = stack.pop(str(row - 1))

        row = len(stack)
        stack[str(row)] = first ^ second

        # NOTE: GAS
        gas = gas_table[opcode]
    elif opcode == 'NOT':
        row = len(stack) - 1
        first = stack.pop(str(row))

        row = len(stack)
        stack[str(row)] = (~first) & UNSIGNED_BOUND_NUMBER

        # NOTE: GAS
        gas = gas_table[opcode]
    elif opcode == 'BYTE':
        row = len(stack) - 1
        first = stack.pop(str(row))
        second = stack.pop(str(row - 1))
        byte_index = 32 - first - 1

        if first >= 32 or first < 0:
            computed = 0
        else:
            computed = second & (255 << (8 * byte_index))
            computed >>= (8 * byte_index)

        row = len(stack)
        stack[str(row)] = computed

        # NOTE: GAS
        gas = gas_table[opcode]
    elif opcode in ['SHA3', 'KECCAK256']:
        row = len(stack) - 1
        position = stack.pop(str(row))
        length = stack.pop(str(row - 1))
        stop = position + length

        val = 0
        for i in memory:
            if position <= int(i) <= stop:
                val += memory[i]
        computed = int(sha3.sha3_224(str(val).encode('utf-8')).hexdigest(), 16)

        row = len(stack)
        stack[str(row)] = computed

        # NOTE: GAS
        gas = 30 + 6 * ((len(hex(length)) - 2) / 4)
    elif opcode == 'ADDRESS':
        row = len(stack)
        stack[str(row)] = get_model_var('Ia')

        # NOTE: GAS
        gas = gas_table[opcode]
    elif opcode == 'BALANCE':
        row = len(stack) - 1
        address = stack.pop(str(row))

        var = get_gen().gen_balance_var(line)
        val = get_model_var(var)

        row = len(stack)
        stack[str(row)] = val

        # NOTE: GAS
        gas = gas_table[opcode]
    elif opcode == 'CALLER':
        var = get_gen().gen_caller_var(line)
        val = get_model_var(var)

        row = len(stack)
        stack[str(row)] = val

        # NOTE: GAS
        gas = gas_table[opcode]
    elif opcode == "ORIGIN":
        var = get_gen().gen_origin_var(line)

        val = get_model_var(var)

        row = len(stack)
        stack[str(row)] = val

        # NOTE: GAS
        gas = gas_table[opcode]
    elif opcode == 'CALLVALUE':
        var = get_gen().gen_value_var(line)
        val = get_model_var(var)

        row = len(stack)
        stack[str(row)] = val

        # NOTE: GAS
        gas = gas_table[opcode]
    elif opcode == 'CALLDATALOAD':
        # FIXME: handle var
        row = len(stack) - 1
        position = stack.pop(str(row))

        var = get_gen().gen_data_var(line)
        val = get_model_var(var)

        row = len(stack)
        stack[str(row)] = val

        # NOTE: GAS
        gas = gas_table[opcode]
    elif opcode == 'CALLDATASIZE':
        var = get_gen().gen_data_size(line)
        val = get_model_var(var)

        row = len(stack)
        stack[str(row)] = val

        # NOTE: GAS
        gas = gas_table[opcode]
    elif opcode == "CALLDATACOPY":
        row = len(stack) - 1
        mem_p = stack.pop(str(row))
        msg_p = stack.pop(str(row - 1))
        num_bytes = stack.pop(str(row - 2))

        var = get_gen().gen_data_var(line)
        val = get_model_var(var)
        memory[str(mem_p)] = val

        # NOTE: GAS
        gas = 2 + 3 * (len(hex(num_bytes)) - 2)
    elif opcode == 'CODESIZE':
        var = get_gen().gen_data_size(line)
        val = get_model_var(var)

        row = len(stack)
        stack[str(row)] = val

        # NOTE: GAS
        gas = gas_table[opcode]
    elif opcode == 'CODECOPY':
        row = len(stack) - 1
        mem_p = stack.pop(str(row))
        msg_p = stack.pop(str(row - 1))
        num_bytes = stack.pop(str(row - 2))

        var = get_gen().gen_code_var(line)
        val = get_model_var(var)
        memory[str(mem_p)] = val

        # NOTE: GAS
        gas = 2 + 3 * (len(hex(num_bytes)) - 2)
    elif opcode == 'GASPRICE':
        var = get_gen().gen_gas_price_var(line)
        val = get_model_var(var)

        row = len(stack)
        stack[str(row)] = val

        # NOTE: GAS
        gas = gas_table[opcode]
    elif opcode == 'RETURNDATACOPY':
        row = len(stack) - 1
        z = stack.pop(str(row))
        y = stack.pop(str(row - 1))
        x = stack.pop(str(row - 2))

        var = get_gen().gen_data_var(line)
        val = get_model_var(var)
        memory[str(z)] = val

        # NOTE: GAS
        gas = 2 + 3 * (len(hex(x)) - 2)
    elif opcode == 'RETURNDATASIZE':
        var = get_gen().gen_data_size(line)
        val = get_model_var(var)

        row = len(stack)
        stack[str(row)] = val

        # NOTE: GAS
        gas = gas_table[opcode]
    elif opcode == 'NUMBER':
        val = get_model_var('BLOCKNUMBER')

        row = len(stack)
        stack[str(row)] = val

        # NOTE: GAS
        gas = gas_table[opcode]
    elif opcode == 'POP':
        row = len(stack) - 1
        stack.pop(str(row))

        # NOTE: GAS
        gas = gas_table[opcode]
    elif opcode == 'MLOAD':
        row = len(stack) - 1
        address = stack.pop(str(row))
        if str(address) in memory:
            value = memory[str(address)]
        else:
            value = 0
        # value = memory[str(address)]

        row = len(stack)
        stack[str(row)] = value

        # NOTE: GAS
        gas = gas_table[opcode]
    elif opcode == 'MSTORE':
        row = len(stack) - 1
        address = stack.pop(str(row))
        value = stack.pop(str(row - 1))
        memory[str(address)] = value

        # NOTE: GAS
        gas = gas_table[opcode]
    elif opcode == 'SLOAD':
        row = len(stack) - 1
        address = stack.pop(str(row))
        if str(address) in storage:
            value = storage[str(address)]
        else:
            value = 0

        row = len(stack)
        stack[str(row)] = value

        # NOTE: GAS
        gas = gas_table[opcode]
    elif opcode == 'SSTORE':
        row = len(stack) - 1
        address = stack.pop(str(row))
        value = stack.pop(str(row - 1))

        # NOTE: GAS
        c1 = False if str(address) in storage.keys() else True
        c2 = False if value == 0 else True

        gas = 20000 if c1 and c2 else 5000

        storage[str(address)] = value
    elif opcode == 'JUMP':
        row = len(stack) - 1
        next_tag = stack.pop(str(row))

        # NOTE: GAS
        gas = gas_table[opcode]
    elif opcode == 'JUMPI':
        row = len(stack) - 1
        next_tag = stack.pop(str(row))
        constraint = stack.pop(str(row - 1))

        # NOTE: GAS
        gas = gas_table[opcode]
    elif opcode == 'GAS':
        var = get_gen().gen_gas_var(line)
        val = get_model_var(var)

        row = len(stack)
        stack[str(row)] = val

        # NOTE: GAS
        gas = gas_table[opcode]
    elif opcode.startswith('PUSH', 0):
        if len(instruction_set) > 1:
            if instruction_set[1] == '[tag]':
                pushed_value = int(instruction_set[2])
            elif instruction_set[1] == 'data':
                pushed_value = int(str(instruction_set[2]), 16)
            else:
                pushed_value = int(str(instruction_set[1]), 16)
        else:
            if instruction_set[0] == 'PUSHDEPLOYADDRESS':
                var = get_gen().gen_arbitrary_address_var(line)
                val = get_model_var(var)
                pushed_value = val
            else:
                raise ValueError('PUSH ERROR')

        row = len(stack)
        stack[str(row)] = pushed_value

        # NOTE: GAS
        gas = gas_table['PUSH']
    elif opcode.startswith('DUP', 0):
        position = len(stack) - int(opcode[3:], 10)

        duplicate_value = stack[str(position)]
        row = len(stack)
        stack[str(row)] = duplicate_value

        # NOTE: GAS
        gas = gas_table['DUP']
    elif opcode.startswith('SWAP', 0):
        position = len(stack) - 1 - int(opcode[4:], 10)

        temp_value = stack[str(position)]
        row = len(stack) - 1
        stack[str(position)] = stack[str(row)]
        stack[str(row)] = temp_value

        # NOTE: GAS
        gas = gas_table['SWAP']
    elif opcode in ('LOG0', 'LOG1', 'LOG2', 'LOG3', 'LOG4'):
        num_of_pops = 2 + int(opcode[3:])

        row = len(stack) - 1
        offset = stack.pop(str(row))
        word = stack.pop(str(row - 1))
        for _ in range(int(opcode[3:])):
            num_of_pops -= 1
            row = len(stack) - 1
            pop_value = stack.pop(str(row))

        # NOTE: GAS
        gas = (int(opcode[3:]) + 1) * 375 + (8 * (len(hex(word)) - 2))
    elif opcode == 'CALL':
        row = len(stack) - 1
        out_gas = stack.pop(str(row))
        addr = stack.pop(str(row - 1))
        out_value = stack.pop(str(row - 2))
        in_position = stack.pop(str(row - 3))
        in_length = stack.pop(str(row - 4))
        out_position = stack.pop(str(row - 5))
        out_length = stack.pop(str(row - 6))

        var = get_gen().gen_call_success(line)
        val = get_model_var(var)

        row = len(stack)
        stack[str(row)] = val

        # NOTE: GAS
        gas = gas_table[opcode]
        if out_value != 0:
            gas += 9000
    elif opcode == 'CALLCODE':
        row = len(stack) - 1
        out_gas = stack.pop(str(row))
        recipient = stack.pop(str(row - 1))
        out_wei = stack.pop(str(row - 2))
        in_value = stack.pop(str(row - 3))
        in_size = stack.pop(str(row - 4))
        out_value = stack.pop(str(row - 5))
        out_size = stack.pop(str(row - 6))

        var = get_gen().gen_call_success(line)
        val = get_model_var(var)

        row = len(stack)
        stack[str(row)] = val

        # NOTE: GAS
        gas = gas_table[opcode]
    elif opcode in ['DELEGATECALL', 'STATICCALL']:
        row = len(stack) - 1
        out_gas = stack.pop(str(row))
        recipient = stack.pop(str(row - 1))
        in_value = stack.pop(str(row - 2))
        in_size = stack.pop(str(row - 3))
        out_value = stack.pop(str(row - 4))
        out_size = stack.pop(str(row - 5))

        var = get_gen().gen_arbitrary_var(line)
        val = get_model_var(var)

        row = len(stack)
        stack[str(row)] = val

        # NOTE: GAS
        gas = gas_table[opcode]
    elif opcode == 'RETURN':
        row = len(stack) - 1
        stack.pop(str(row))
        stack.pop(str(row - 1))

        # NOTE: GAS
        gas = gas_table[opcode]
    elif opcode == 'CREATE':
        row = len(stack) - 1
        wei = stack.pop(str(row))
        position = stack.pop(str(row - 1))
        length = stack.pop(str(row - 2))

        var = get_gen().gen_arbitrary_var(line)
        val = get_model_var(var)

        row = len(stack)
        stack[str(row)] = val

        # NOTE: GAS
        gas = gas_table[opcode]
    elif opcode == 'EXTCODESIZE':
        row = len(stack) - 1
        address = stack.pop(str(row))

        var = get_gen().gen_code_size_var(address, line)
        val = get_model_var(var)

        row = len(stack)
        stack[str(row)] = val

        # NOTE: GAS
        gas = gas_table[opcode]
    elif opcode == 'BLOCKHASH':
        row = len(stack) - 1
        block_num = stack.pop(str(row))

        var = get_gen().gen_hash_var(block_num, line)
        val = get_model_var(var)

        row = len(stack)
        stack[str(row)] = val

        # NOTE: GAS
        gas = gas_table[opcode]
    elif opcode == 'SELFDESTRUCT':
        row = len(stack) - 1
        stack.pop(str(row))

        # NOTE: GAS
        var = 'Inewaccount_%s' % line
        val = get_model_var(var)
        gas = 5000 if val <= 0 else 30000
    else:
        raise Exception('UNKNOWN INSTRUCTION:', instruction, line)
    return state, gas


def get_model_var(var):
    global model

    model_vars = model.decls()
    val = None
    for v in model_vars:
        if str(v) == var:
            val = model[v]
    if val is None:
        # print('[MODEL]:', var, model_vars)
        return get_model_var(get_same_var(var))
        # raise ValueError('No Model Variable')
    return val
