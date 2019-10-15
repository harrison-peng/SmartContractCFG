nodes = []
edges = []
node_addr_li = []
addr_line_dict = dict()
count_edge = dict()


def cfg_construction(opcode_data, contract_name):
    global nodes
    global edges
    global addr_line_dict
    global node_addr_li

    nodes = []
    edges = []
    addr_line_dict = dict()

    print('''\n[INFO] Constructing CFG for contract '%s'. ''' % contract_name)

    opcode_list = opcode_data.split('\n')
    for i in range(len(opcode_list)):
        opcode_list[i] = (i, opcode_list[i])

    for index, line in opcode_list:
        code_set = line.rstrip().split(' ')
        pc = int(code_set[0].replace(':', ''))
        s = code_set[1:]
        if s[0] == 'JUMPDEST':
            addr_line_dict.update({pc: index})

    cfg_implement(opcode_list, 0, 0, list(), list(), True)

    for addr in addr_line_dict:
        if addr not in node_addr_li:
            cfg_implement(opcode_list, addr_line_dict[addr], addr, [0], list(), False)

    return nodes, edges


def cfg_implement(opcode_list, start_idx, curr_addr, stack, path, exec_mode):
    global nodes
    global edges
    global addr_line_dict
    global count_edge

    segment_ins = ['JUMPDEST', 'JUMP', 'JUMPI', 'STOP', 'REVERT', 'INVALID', 'RETURN', 'SELFDESTRUCT']

    node_content = init_node_content()

    opcode_sublist = opcode_list[start_idx:]
    for index, line in opcode_sublist:
        code_set = line.rstrip().split(' ')
        pc = int(code_set[0].replace(':', ''))
        s = code_set[1:]

        # if curr_addr in [7779, 7742]:
        #     print(pc, curr_addr, s[0], stack)
        #     print(path, '\n')

        jump_addr = None
        if exec_mode:
            stack, jump_addr = ins_sim(stack, s, pc)

        if s[0] == '':
            continue
        elif s[0] in segment_ins:
            if s[0] == 'JUMPDEST':
                path.append(pc)
                if node_content['ins']:
                    # NOTE: node content is not empty
                    if not is_node_exist(curr_addr):
                        add_node(curr_addr, node_content)
                    if exec_mode and not is_edge_exist(curr_addr, pc):
                        add_edge(curr_addr, pc)
                    node_content = init_node_content()

                curr_addr = pc
                node_content['ins'].append(line)
            elif s[0] == 'JUMP':
                node_content['ins'].append(line)

                if not is_node_exist(curr_addr):
                    add_node(curr_addr, node_content)

                if exec_mode:
                    jump_idx = addr_line_dict[jump_addr]
                    if not is_edge_exist(curr_addr, jump_addr):
                        add_edge(curr_addr, jump_addr)
                    cfg_implement(opcode_list, jump_idx, jump_addr, list(stack), path, exec_mode)

                return
            elif s[0] == 'JUMPI':
                node_content['ins'].append(line)

                if not is_node_exist(curr_addr):
                    add_node(curr_addr, node_content)

                if exec_mode:
                    jump_addr_true = jump_addr
                    jump_idx_true = addr_line_dict[jump_addr_true]
                    jump_addr_false = pc + 1
                    jump_idx_false = index + 1
                    stack_true = list(stack)
                    stack_false = list(stack)
                    path_true = list(path)
                    path_false = list(path)
                    if not is_edge_exist(curr_addr, jump_addr_true):
                        add_edge(curr_addr, jump_addr_true)
                    if jump_addr_true not in path:
                        cfg_implement(opcode_list, jump_idx_true, jump_addr_true, stack_true, path_true, exec_mode)

                    if not is_edge_exist(curr_addr, jump_addr_false):
                        add_edge(curr_addr, jump_addr_false)
                    if jump_addr_false not in path:
                        cfg_implement(opcode_list, jump_idx_false, jump_addr_false, stack_false, path_false, exec_mode)
                return
            else:
                if not node_content['ins']:
                    curr_addr = pc

                node_content['ins'].append(line)
                if not is_node_exist(curr_addr):
                    add_node(curr_addr, node_content)
                return
        else:
            if not node_content['ins']:
                # NOTE: node content is empty -> from JUMPI
                curr_addr = pc
                path.append(pc)
            node_content['ins'].append(line)


def is_edge_exist(from_addr, to_addr):
    global edges
    global count_edge

    for edge in edges:
        jump_pair = list(map(int, edge[0]))
        if from_addr == jump_pair[0] and to_addr == jump_pair[1]:
            return True
    return False


def is_node_exist(addr):
    global nodes

    for node in nodes:
        tag_in_node = node['addr']
        if tag_in_node == addr:
            return True
    return False


def add_node(addr, node):
    global nodes
    global node_addr_li

    node_addr_li.append(addr)
    node['addr'] = addr
    nodes.append(node)


def add_edge(from_addr, to_addr):
    global edges
    edges.append(((str(from_addr), str(to_addr)),
                  {'label': list(),
                   'color': 'blue'}))


def init_node_content():
    return {'addr': None, 'ins': list(), 'gas': None, 'state': list()}


def ins_sim(stack, instruction, line):
    opcode = instruction[0]
    addr = None

    if opcode in ['INVALID', 'STOP', 'REVERT', 'JUMPDEST']:
        pass
    elif opcode == 'TIMESTAMP':
        stack.append('TIMESTAMP')
    elif opcode == 'ADD':
        first = stack.pop()
        second = stack.pop()
        stack.append('ADD')
    elif opcode == 'MUL':
        first = stack.pop()
        second = stack.pop()
        stack.append('MUL')
    elif opcode == 'SUB':
        first = stack.pop()
        second = stack.pop()
        stack.append('SUB')
    elif opcode == 'DIV':
        first = stack.pop()
        second = stack.pop()
        stack.append('DIV')
    elif opcode == 'SDIV':
        first = stack.pop()
        second = stack.pop()
        stack.append('SDIV')
    elif opcode == 'MOD':
        first = stack.pop()
        second = stack.pop()
        stack.append('MOD')
    elif opcode == 'SMOD':
        first = stack.pop()
        second = stack.pop()
        stack.append('SMOD')
    elif opcode == 'ADDMOD':
        first = stack.pop()
        second = stack.pop()
        third = stack.pop()
        stack.append('ADDMOD')
    elif opcode == 'MULMOD':
        first = stack.pop()
        second = stack.pop()
        third = stack.pop()
        stack.append('MULMOD')
    elif opcode == 'EXP':
        first = stack.pop()
        second = stack.pop()
        stack.append('EXP')
    elif opcode == 'SIGNEXTEND':
        first = stack.pop()
        second = stack.pop()
        stack.append('SIGNEXTEBD')
    elif opcode == 'LT':
        first = stack.pop()
        second = stack.pop()
        stack.append('LT')
    elif opcode == 'GT':
        first = stack.pop()
        second = stack.pop()
        stack.append('GT')
    elif opcode == 'SLT':
        first = stack.pop()
        second = stack.pop()
        stack.append('SLT')
    elif opcode == 'SGT':
        first = stack.pop()
        second = stack.pop()
        stack.append('SGT')
    elif opcode == 'EQ':
        first = stack.pop()
        second = stack.pop()
        stack.append('EQ')
    elif opcode == 'ISZERO':
        first = stack.pop()
        stack.append('ISZERO')
    elif opcode == 'AND':
        first = stack.pop()
        second = stack.pop()
        if isinstance(first, int) and isinstance(second, int):
            stack.append(first & second)
        else:
            stack.append('AND')
    elif opcode == 'OR':
        first = stack.pop()
        second = stack.pop()
        if isinstance(first, int) and isinstance(second, int):
            stack.append(first | second)
        else:
            stack.append('AND')
    elif opcode == 'XOR':
        first = stack.pop()
        second = stack.pop()
        stack.append('XOR')
    elif opcode == 'NOT':
        first = stack.pop()
        if isinstance(first, int):
            stack.append(~first)
        else:
            stack.append('NOT')
    elif opcode == 'BYTE':
        first = stack.pop()
        second = stack.pop()
        stack.append('BYTE')
    elif opcode in ['SHA3', 'KECCAK256']:
        first = stack.pop()
        second = stack.pop()
        stack.append('SHA3')
    elif opcode == 'ADDRESS':
        stack.append('ADDRESS')
    elif opcode == 'BALANCE':
        first = stack.pop()
        stack.append('BALANCE')
    elif opcode == 'CALLER':
        stack.append('CALLER')
    elif opcode == "ORIGIN":
        stack.append('ORIGIN')
    elif opcode == 'CALLVALUE':
        stack.append('CALLVALUE')
    elif opcode == 'CALLDATALOAD':
        first = stack.pop()
        stack.append('CALLDATALOAD')
    elif opcode == 'CALLDATASIZE':
        stack.append('CALLDATASIZE')
    elif opcode == "CALLDATACOPY":
        first = stack.pop()
        second = stack.pop()
        third = stack.pop()
    elif opcode == 'CODESIZE':
        stack.append('CODESIZE')
    elif opcode == 'CODECOPY':
        first = stack.pop()
        second = stack.pop()
        third = stack.pop()
    elif opcode == 'GASPRICE':
        stack.append('GASPRICE')
    elif opcode == 'RETURNDATACOPY':
        first = stack.pop()
        second = stack.pop()
        third = stack.pop()
    elif opcode == 'RETURNDATASIZE':
        stack.append('RETURNDATASIZE')
    elif opcode == 'NUMBER':
        stack.append('NUMBER')
    elif opcode == 'POP':
        stack.pop()
    elif opcode == 'MLOAD':
        first = stack.pop()
        stack.append('MLOAD')
    elif opcode == 'MSTORE':
        first = stack.pop()
        second = stack.pop()
    elif opcode == 'SLOAD':
        first = stack.pop()
        stack.append('SLOAD')
    elif opcode == 'SSTORE':
        first = stack.pop()
        second = stack.pop()
    elif opcode == 'JUMP':
        addr = stack.pop()
    elif opcode == 'JUMPI':
        addr = stack.pop()
        second = stack.pop()
    elif opcode == 'GAS':
        stack.append('GAS')
    elif opcode.startswith('PUSH', 0):
        stack.append(int(instruction[1], 16))
    elif opcode.startswith('DUP', 0):
        idx = len(stack) - int(opcode[3:], 10)
        stack.append(stack[idx])
        # if idx < 0:
        #     stack.append('DUP')
        # else:
        #     stack.append(stack[idx])
    elif opcode.startswith('SWAP', 0):
        idx_1 = len(stack) - 1
        idx_2 = len(stack) - 1 - int(opcode[4:], 10)
        stack[idx_1], stack[idx_2] = stack[idx_2], stack[idx_1]
        # if idx_2 < 0:
        #     stack.append('SWAP')
        # else:
        #     stack[idx_1], stack[idx_2] = stack[idx_2], stack[idx_1]
    elif opcode in ('LOG0', 'LOG1', 'LOG2', 'LOG3', 'LOG4'):
        first = stack.pop()
        second = stack.pop()
        for _ in range(int(opcode[3:])):
            stack.pop()
    elif opcode == 'CALL':
        first = stack.pop()
        second = stack.pop()
        third = stack.pop()
        fourth = stack.pop()
        fifth = stack.pop()
        sixth = stack.pop()
        seventh = stack.pop()
        stack.append('CALL')
    elif opcode == 'CALLCODE':
        first = stack.pop()
        second = stack.pop()
        third = stack.pop()
        fourth = stack.pop()
        fifth = stack.pop()
        sixth = stack.pop()
        seventh = stack.pop()
        stack.append('CALLCODE')
    elif opcode in ['DELEGATECALL', 'STATICCALL']:
        first = stack.pop()
        second = stack.pop()
        third = stack.pop()
        fourth = stack.pop()
        fifth = stack.pop()
        sixth = stack.pop()
        stack.append('DELEGATECALL')
    elif opcode == 'RETURN':
        first = stack.pop()
        second = stack.pop()
    elif opcode == 'CREATE':
        first = stack.pop()
        second = stack.pop()
        third = stack.pop()
        stack.append('CREATE')
    elif opcode == 'EXTCODESIZE':
        first = stack.pop()
        stack.append('EXTCODESIZE')
    elif opcode == 'BLOCKHASH':
        first = stack.pop()
        stack.append('BLOCKHASH')
    elif opcode == 'SELFDESTRUCT':
        first = stack.pop()
    else:
        raise Exception('UNKNOWN INSTRUCTION:', instruction, line)
    if addr and not isinstance(addr, int):
        raise ValueError('ERROR ADDRESS:', line, addr, stack)
    return stack, addr
