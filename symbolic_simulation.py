from gas_price import *
import os
import re
import se_ins as se
import symbolic_simulation_old as ss
import state_simulation

count_sim = 0
stack = []
storage = []
memory = []
nodes = []
edges = []
count_path = 0
tag_run_time = dict()


def symbolic_simulation(nodes_in, edges_in):
    global nodes
    global edges
    global count_path
    global tag_run_time

    nodes = nodes_in
    edges = edges_in
    f_con = []
    t_con = []
    con = []
    q = []
    conq = []
    sym_mem = []
    gasq = []
    # gas_sum, c_nodes, c_edges, q = ss.stack_status_constraint(sym_mem, nodes, edges, '0',
    #                                                        '', f_con, t_con, 0,
    #                                                        0, 0, con, q,
    #                                                        0, conq, gasq)

    # print('gas SUM = ', gas_sum)


    count_path = 0
    tag_run_time = dict()
    state = [{}, {}, {}]
    gas = [0, '']
    symbolic_implement(state, gas, '0', '', ['0'], False, 0)
    # print('[INFO] Find', count_path, 'path')

    # for key in tag_run_time:
    #     if tag_run_time[key] > 9:
    #         print('[OVER]:', key, tag_run_time[key])

    return nodes, edges


def symbolic_implement(state, gas, tag, prev_tag, tag_stack, has_jump_in, jump_in_num):
    """
    param:
    [tag]: the tag of the node to run the symbolic simulation
    [prev_tag]: the tag of the previous node
    [tag_stack]: the stack of the tag number
    [has_jump_in]: T/F, is there has the first JUMP (in)
    [jump_in_num]: the number of the JUMP [in]
    """
    global stack
    global nodes
    global edges
    global count_path
    global tag_run_time

    prev_ins = ''
    count_push = 0

    # NOTE: if the node run more than 10 times, stop -> cycle
    try:
        run_time = tag_run_time[tag]
        if run_time > 10:
            tag_run_time.update({tag: 0})
            return
        else:
            run_time += 1
            tag_run_time.update({tag: run_time})
    except:
        tag_run_time.update({tag: 1})

    for node in nodes:
        if node[0] == tag:
            node_gas = [0, '']

            # NOTE: remove the curr tag in tag stack
            if tag_stack[-1] == tag:
                tag_stack.pop()

            label = node[1].get('label')
            # NOTE: remove 'TAG' in label ([0, 1])
            ins_list = label.split('\n')[2:]

            for ins in ins_list:
                ins_set = ins.split(': ')
                line = ins_set[0]
                opcode = ins_set[1]

                if opcode.split(' ')[0] == 'tag':
                    '''
                    tag:
                    need not to handle 'tag'
                    '''
                    pass
                elif opcode in ['JUMP', 'JUMP [in]']:
                    '''
                    JUMP and JUMP [in]: 
                    find the next node in prev ins, and go to next node
                    '''

                    # TODO: stack simulation
                    state, ins_gas = state_simulation.state_simulation(opcode, state)
                    if isinstance(ins_gas, int):
                        gas[0] += ins_gas
                        node_gas[0] += ins_gas
                    else:
                        if gas[1] == '':
                            gas[1] += '(%s)' % str(ins_gas)
                        else:
                            gas[1] += ' + (%s)' % str(ins_gas)
                        if node_gas[1] == '':
                            node_gas[1] += '(%s)' % str(ins_gas)
                        else:
                            node_gas[1] += ' + (%s)' % str(ins_gas)

                    # NOTE: update gas of the node on CFG
                    node = node_add_gas(node, node_gas)

                    if opcode == 'JUMP [in]':
                        jump_in_num -= 1

                    # NOTE: check if has jump in
                    if count_push > 1:
                        has_jump_in = True

                    # NOTE: check if previous ins is PUSH [tag]
                    if prev_ins.split(' ')[0] == 'PUSH' and prev_ins.split(' ')[1] == '[tag]':
                        # NOTE: remove the tag of previous ins (will add later)
                        tag_stack.pop()

                        next_tag = prev_ins.split(' ')[2]
                        for index, edge in enumerate(edges):
                            if edge[0][0] == tag and edge[0][1] == next_tag:
                                edges[index] = edge_change_color(edge)
                                tag_stack.append(next_tag)
                                # NOTE: if next_tag == prev_tag -> there is a cycle, so don't run it
                                if int(next_tag) != int(prev_tag):
                                    return symbolic_implement(state, gas, next_tag, tag, tag_stack, has_jump_in, jump_in_num)
                                else:
                                    return
                    else:
                        next_tag = tag_stack[-1]
                        for index, edge in enumerate(edges):
                            if edge[0][0] == tag and edge[0][1] == next_tag:
                                edges[index] = edge_change_color(edge)
                                # NOTE: if next_tag == prev_tag -> there is a cycle, so don't run it
                                if int(next_tag) != int(prev_tag):
                                    return symbolic_implement(state, gas, next_tag, tag, tag_stack, has_jump_in, jump_in_num)
                                else:
                                    return
                elif opcode == 'JUMP [out]':
                    '''
                    JUMP [out]:
                    get the next node form the tag_stack, and go to the next node
                    '''
                    # TODO: stack simulation
                    state, ins_gas = state_simulation.state_simulation(opcode, state)
                    if isinstance(ins_gas, int):
                        gas[0] += ins_gas
                        node_gas[0] += ins_gas
                    else:
                        if gas[1] == '':
                            gas[1] += '(%s)' % str(ins_gas)
                        else:
                            gas[1] += ' + (%s)' % str(ins_gas)
                        if node_gas[1] == '':
                            node_gas[1] += '(%s)' % str(ins_gas)
                        else:
                            node_gas[1] += ' + (%s)' % str(ins_gas)

                    # NOTE: update gas of the node on CFG
                    node = node_add_gas(node, node_gas)

                    # NOTE: if jump_in_num > 0 -> jump_in_number - 1 else turn has_jump_in to False
                    if jump_in_num == 0:
                        has_jump_in = False
                    else:
                        jump_in_num -= 1

                    # NOTE: if len(tag_stack) == 0 -> it comes from JUMPI second path, so don't run this way
                    if len(tag_stack) > 0:
                        next_tag = tag_stack[-1]
                        for index, edge in enumerate(edges):
                            if edge[0][0] == tag and edge[0][1] == next_tag:
                                edges[index] = edge_change_color(edge)
                                return symbolic_implement(state, gas, next_tag, tag, tag_stack, has_jump_in, jump_in_num)
                elif opcode == 'JUMPI':
                    '''
                    JUMPI:
                    there are two path to run
                        first -> the JUMP path (always with JUMP IN)
                        second -> always stop in the next node
                    '''

                    # TODO: stack simulation
                    state, ins_gas = state_simulation.state_simulation(opcode, state)
                    if isinstance(ins_gas, int):
                        gas[0] += ins_gas
                        node_gas[0] += ins_gas
                    else:
                        if gas[1] == '':
                            gas[1] += '(%s)' % str(ins_gas)
                        else:
                            gas[1] += ' + (%s)' % str(ins_gas)
                        if node_gas[1] == '':
                            node_gas[1] += '(%s)' % str(ins_gas)
                        else:
                            node_gas[1] += ' + (%s)' % str(ins_gas)

                    # NOTE: update gas of the node on CFG
                    node = node_add_gas(node, node_gas)

                    # NOTE: remove the tag in previous ins (will add later)
                    tag_stack.pop()

                    first_tag = ''
                    second_tag = ''

                    # NOTE: create two stack for two path
                    tag_stack_first = []
                    tag_stack_second = []
                    for item in tag_stack:
                        tag_stack_first.append(item)
                        tag_stack_second.append(item)

                    for index, edge in enumerate(edges):
                        if edge[0][0] == tag:
                            edges[index] = edge_change_color(edge)
                            if first_tag == '':
                                first_tag = edge[0][1]

                                # NOTE: if there is JUMP IN and it's second path, remove the JUMP IN tag
                                if has_jump_in and prev_ins.split(' ')[2] != first_tag:
                                    tag_stack_first.pop()

                                tag_stack_first.append(first_tag)
                            else:
                                second_tag = edge[0][1]

                                # NOTE: if there is JUMP IN and it's second path, remove the JUMP IN tag
                                if has_jump_in and prev_ins.split(' ')[2] != second_tag and len(tag_stack_second) > 0:
                                    tag_stack_second.pop()

                                tag_stack_second.append(second_tag)

                    # NOTE: run two path
                    symbolic_implement(state, gas, first_tag, tag, tag_stack_first, has_jump_in, jump_in_num)
                    return symbolic_implement(state, gas, second_tag, tag, tag_stack_second, has_jump_in, jump_in_num)
                elif opcode in ['STOP', 'RETURN', 'REVERT', 'INVALID']:
                    '''
                    STOP, RETURN, REVERT, INVALID:
                    the final node of the path
                    '''

                    # NOTE: update gas of the node on CFG
                    node = node_add_gas(node, node_gas)
                    node = node_add_path_gas_sum(node, gas)

                    # print('[GAS]:', tag, gas)
                    count_path += 1
                    return
                elif line == 'Stack Sum':
                    '''
                    if there isn't any JUMP or JUMPI, there is one way to go,
                    so find the next node in edges and go to there 
                    '''

                    # NOTE: update gas of the node on CFG
                    # node = node_add_gas(node, node_gas)

                    for index, edge in enumerate(edges):
                        if edge[0][0] == tag:
                            edges[index] = edge_change_color(edge)
                            next_tag = edge[0][1]
                            tag_stack.append(next_tag)
                            return symbolic_implement(state, gas, next_tag, tag, tag_stack, has_jump_in, jump_in_num)
                else:
                    # TODO: stack simulation
                    state, ins_gas = state_simulation.state_simulation(opcode, state)
                    if isinstance(ins_gas, int):
                        gas[0] += ins_gas
                        node_gas[0] += ins_gas
                    else:
                        if gas[1] == '':
                            gas[1] += '(%s)' % str(ins_gas)
                        else:
                            gas[1] += ' + (%s)' % str(ins_gas)
                        if node_gas[1] == '':
                            node_gas[1] += '(%s)' % str(ins_gas)
                        else:
                            node_gas[1] += ' + (%s)' % str(ins_gas)

                    # NOTE: if there is PUSH tag, put the tag to tag_stack
                    opcode_set = opcode.split(' ')
                    if opcode_set[0] == 'PUSH' and opcode_set[1] == '[tag]':
                        tag_stack.append(opcode_set[2])
                        count_push += 1
                prev_ins = opcode

            break


def edge_change_color(edge):
    edge_set = edge[0]
    color = edge[1]['color']
    retval = list()
    retval.append(edge_set)
    if color == 'blue':
        retval.append({'label': '', 'color': 'green'})
    elif color == 'green':
        retval.append({'label': '', 'color': 'purple'})
    elif color == 'purple':
        retval.append({'label': '', 'color': 'red'})
    else:
        retval.append({'label': '', 'color': 'black'})
    return tuple(retval)


def node_add_gas(node, gas):
    if not 'Gas: ' in node[1]['label']:
        gas_num = gas[0]
        gas_sym = gas[1]
        if gas_sym == '':
            node[1]['label'] += '\nGas: %s' % gas_num
        else:
            node[1]['label'] += '\nGas: %s' % gas_num
            gas_sym_list = gas_sym.split(' + ')
            start = True
            for item in gas_sym_list:
                if start:
                    start = False
                    node[1]['label'] += '\n+[%s' % item
                else:
                    node[1]['label'] += '\n+%s' % item

            node[1]['label'] += ']'
    return node


def node_add_path_gas_sum(node, gas):
    gas_num = gas[0]
    gas_sym = gas[1]
    node[1]['label'] += '\n'
    if 'Path Gas Sum:' in node[1]['label']:
        node[1]['label'] = node[1]['label'][:-2]

        if gas_sym == '':
            node[1]['label'] += ',\n(%s)]' % gas_num
        else:
            gas_sym_list = gas_sym.split(' + ')
            node[1]['label'] += ',\n(%s' % gas_num
            start = True
            for item in gas_sym_list:
                if start:
                    start = False
                    node[1]['label'] += '+(%s' % item
                else:
                    node[1]['label'] += '\n+%s' % item
            node[1]['label'] += '))]'
    else:
        node[1]['label'] += '\nPath Gas Sum:\n['
        if gas_sym == '':
            node[1]['label'] += '(%s)]' % gas_num
        else:
            gas_sym_list = gas_sym.split(' + ')
            node[1]['label'] += '(%s' % gas_num
            start = True
            for item in gas_sym_list:
                if start:
                    start = False
                    node[1]['label'] += '+(%s' % item
                else:
                    node[1]['label'] += '\n+%s' % item
            node[1]['label'] += '))]'
    return node