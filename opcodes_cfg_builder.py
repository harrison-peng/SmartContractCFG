from state_simulation import state_simulation

nodes = []
edges = []
addr_line_dict = dict()


def cfg_construction(opcode_data, contract_name):
    global nodes
    global edges
    global addr_line_dict

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

    cfg_implement(opcode_list, 0, 0, list())

    return nodes, edges


def cfg_implement(opcode_list, start_idx, curr_addr, stack):
    global nodes
    global edges
    global addr_line_dict

    segment_ins = ['JUMPDEST', 'JUMP', 'JUMPI', 'STOP', 'REVERT', 'INVALID', 'RETURN']

    node_content = init_node_content()

    opcode_sublist = opcode_list[start_idx:]
    for index, line in opcode_sublist:
        code_set = line.rstrip().split(' ')
        pc = int(code_set[0].replace(':', ''))
        s = code_set[1:]

        if s[0] == '':
            continue
        elif s[0] in segment_ins:
            if s[0] == 'JUMPDEST':
                if node_content['ins']:
                    # NOTE: node content is not empty
                    if not is_node_exist(curr_addr):
                        add_node(curr_addr, node_content)
                    if not is_edge_exist(curr_addr, pc):
                        add_edge(curr_addr, pc)
                    node_content = init_node_content()

                curr_addr = pc
                node_content['ins'].append(line)
            elif s[0] == 'JUMP':
                node_content['ins'].append(line)

                if not is_node_exist(curr_addr):
                    add_node(curr_addr, node_content)

                jump_addr = stack.pop()
                jump_idx = addr_line_dict[jump_addr]
                if not is_edge_exist(curr_addr, jump_addr):
                    add_edge(curr_addr, jump_addr)
                    cfg_implement(opcode_list, jump_idx, jump_addr, stack)

                return
            elif s[0] == 'JUMPI':
                node_content['ins'].append(line)

                if not is_node_exist(curr_addr):
                    add_node(curr_addr, node_content)

                jump_addr_true = stack.pop()
                jump_idx_true = addr_line_dict[jump_addr_true]
                jump_addr_false = pc + 1
                jump_idx_false = index + 1
                stack_true = list(stack)
                stack_false = list(stack)
                if not is_edge_exist(curr_addr, jump_addr_true):
                    add_edge(curr_addr, jump_addr_true)
                    cfg_implement(opcode_list, jump_idx_true, jump_addr_true, stack_true)

                if not is_edge_exist(curr_addr, jump_addr_false):
                    add_edge(curr_addr, jump_addr_false)
                    cfg_implement(opcode_list, jump_idx_false, jump_addr_false, stack_false)
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
            if s[0] == 'PUSH2':
                push_addr = int(s[1], 16)
                if push_addr in addr_line_dict:
                    stack.append(push_addr)
            node_content['ins'].append(line)


def is_edge_exist(from_addr, to_addr):
    global edges

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
    node['addr'] = addr
    nodes.append(node)


def add_edge(from_addr, to_addr):
    global edges
    edges.append(((str(from_addr), str(to_addr)),
                  {'label': '',
                   'color': 'blue'}))


def init_node_content():
    return {'addr': None, 'ins': list(), 'gas': None, 'state': None}