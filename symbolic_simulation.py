from gas_price import *
from z3 import *
from var_generator import *
from z3_func import *
import os
import re
import se_ins as se
import symbolic_simulation_old as ss
import json
import state_simulation
import copy
import cfg
import prime_generator as pg
import global_vars

count_sim = 0
stack = []
storage = []
memory = []
nodes = []
edges = []
count_path = 0
tag_run_time = dict()
prime_list = []
prime_check_list = []


def symbolic_simulation(nodes_in, edges_in):
    global nodes
    global edges
    global count_path
    global tag_run_time
    global prime_list
    global prime_check_list

    nodes = nodes_in
    edges = edges_in
    # f_con = []
    # t_con = []
    # con = []
    # q = []
    # conq = []
    # sym_mem = []
    # gasq = []
    # gas_sum, c_nodes, c_edges, q = ss.stack_status_constraint(sym_mem, nodes, edges, '0',
    #                                                        '', f_con, t_con, 0,
    #                                                        0, 0, con, q,
    #                                                        0, conq, gasq)
    # print('gas SUM = ', gas_sum)

    count_path = 0
    tag_run_time = dict()
    state = {'Stack': {}, 'Memory': {}, 'Storage': {}}
    # gas = [0, '']
    gas = 0
    prime_list = pg.generator_prime(2000)
    prime_check_list = pg.generator_prime(2000)
    path_cons = Solver()
    path_cons.set(unsat_core=True)
    pc_track = SolverUnsatCore()
    symbolic_implement(state, gas, path_cons, '0', '', ['0'], False, 0, 1, pc_track)
    print('\n[INFO] Find', count_path, 'path')
    # print('[PRIME]:', prime_list)

    # for key in tag_run_time:
    #     if tag_run_time[key] > 9:
    #         print('[OVER]:', key, tag_run_time[key])

    return nodes, edges


def symbolic_implement(state, gas, path_cons,
                       tag, prev_tag, tag_stack,
                       has_jump_in, jump_in_num, path_label, pc_track):
    # print('[TAG]:', tag)
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
    global prime_list

    prev_ins = ''
    count_push = 0

    # NOTE: if the node run more than 10 times, stop -> cycle
    try:
        run_time = tag_run_time[tag]
        # if run_time > 10:
        #     tag_run_time.update({tag: 0})
        #     return
        # else:
        #     run_time += 1
        #     tag_run_time.update({tag: run_time})
        run_time += 1
        tag_run_time.update({tag: run_time})
    except:
        tag_run_time.update({tag: 1})

    for node in nodes:
        if node[0] == tag:
            # node_gas = [0, '']
            node_gas = 0

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

                if tag == '11':
                    print('[SS]:', ins, state['Stack'])
                    print('[SS1]:', ins, state['Memory'])
                    print('[SS2]:', ins, gas)

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

                    # NOTE: stack simulation
                    state, ins_gas, path_constraint = state_simulation.state_simulation(opcode, state)

                    if is_expr(gas):
                        gas = simplify(gas + ins_gas)
                    else:
                        gas = gas + ins_gas
                    if is_expr(node_gas):
                        node_gas = simplify(node_gas + ins_gas)
                    else:
                        node_gas = node_gas + ins_gas

                    # NOTE: update gas of the node on CFG
                    node = node_add_gas(node, node_gas)
                    node = node_add_path_gas_sum(node, gas)

                    # NOTE: Add the state to the node on CFG
                    new_state = dict()
                    for key, val in state.items():
                        in_new_state = dict()
                        for key1, val1 in val.items():
                            in_new_state[key1] = val1
                        new_state[key] = in_new_state
                    node, convergence = node_add_state(node, new_state, path_label, tag)

                    # NOTE: if the state is same with previous one, then it's convergence --> stop
                    if convergence:
                        return

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
                                    return symbolic_implement(state, gas, path_cons,
                                                              next_tag, tag, tag_stack,
                                                              has_jump_in, jump_in_num, path_label, pc_track)
                                else:
                                    return
                    else:
                        next_tag = tag_stack[-1]
                        for index, edge in enumerate(edges):
                            if edge[0][0] == tag and edge[0][1] == next_tag:
                                edges[index] = edge_change_color(edge)
                                # NOTE: if next_tag == prev_tag -> there is a cycle, so don't run it
                                if int(next_tag) != int(prev_tag):
                                    return symbolic_implement(state, gas, path_cons,
                                                              next_tag, tag, tag_stack,
                                                              has_jump_in, jump_in_num, path_label, pc_track)
                                else:
                                    return
                elif opcode == 'JUMP [out]':
                    '''
                    JUMP [out]:
                    get the next node form the tag_stack, and go to the next node
                    '''
                    # NOTE: stack simulation
                    state, ins_gas, path_constraint = state_simulation.state_simulation(opcode, state)

                    if is_expr(gas):
                        gas = simplify(gas + ins_gas)
                    else:
                        gas = gas + ins_gas
                    if is_expr(node_gas):
                        node_gas = simplify(node_gas + ins_gas)
                    else:
                        node_gas = node_gas + ins_gas

                    # NOTE: update gas of the node on CFG
                    node = node_add_gas(node, node_gas)
                    node = node_add_path_gas_sum(node, gas)

                    # NOTE: Add the state to the node on CFG
                    new_state = dict()
                    for key, val in state.items():
                        in_new_state = dict()
                        for key1, val1 in val.items():
                            in_new_state[key1] = val1
                        new_state[key] = in_new_state
                    node, convergence = node_add_state(node, new_state, path_label, tag)

                    # NOTE: if the state is same with previous one, then it's convergence --> stop
                    if convergence:
                        return

                    # NOTE: if jump_in_num > 0 -> jump_in_number - 1 else turn has_jump_in to False
                    if jump_in_num == 0:
                        has_jump_in = False
                    else:
                        jump_in_num -= 1

                    # NOTE: if len(tag_stack) == 0 -> it comes from JUMPI second path, so don't run this way
                    if len(tag_stack) > 0:
                        # NOTE: make up the missed edge
                        edge_exist = cfg.is_edge_exist(int(tag), int(tag_stack[-1]))
                        if not edge_exist:
                            edges.append(((str(tag), str(tag_stack[-1])),
                                          {'label': '',
                                           'color': 'blue'}))

                        next_tag = tag_stack[-1]
                        for index, edge in enumerate(edges):
                            if edge[0][0] == tag and edge[0][1] == next_tag:
                                edges[index] = edge_change_color(edge)
                                return symbolic_implement(state, gas, path_cons,
                                                          next_tag, tag, tag_stack,
                                                          has_jump_in, jump_in_num, path_label, pc_track)
                elif opcode == 'JUMPI':
                    '''
                    JUMPI:
                    there are two path to run
                        first -> the JUMP path (always with JUMP IN)
                        second -> always stop in the next node
                    '''
                    go_true = True
                    go_false = True
                    path_cons_1 = path_cons.translate(main_ctx())
                    path_cons_2 = path_cons.translate(main_ctx())
                    pc_track_1 = SolverUnsatCore()
                    pc_track_1.set_count(pc_track.get_count())
                    pc_track_2 = SolverUnsatCore()
                    pc_track_2.set_count(pc_track.get_count())

                    # NOTE: stack simulation
                    state, ins_gas, path_constraint = state_simulation.state_simulation(opcode, state)

                    if is_expr(gas):
                        gas = simplify(gas + ins_gas)
                    else:
                        gas = gas + ins_gas
                    if is_expr(node_gas):
                        node_gas = simplify(node_gas + ins_gas)
                    else:
                        node_gas = node_gas + ins_gas

                    # NOTE: update gas of the node on CFG
                    node = node_add_gas(node, node_gas)
                    node = node_add_path_gas_sum(node, gas)

                    # NOTE: Add the state to the node on CFG
                    new_state = dict()
                    for key, val in state.items():
                        in_new_state = dict()
                        for key1, val1 in val.items():
                            in_new_state[key1] = val1
                        new_state[key] = in_new_state
                    node, convergence = node_add_state(node, new_state, path_label, tag)

                    # NOTE: if the state is same with previous one, then it's convergence --> stop
                    if convergence:
                        return

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

                            # NOTE: add path constraints to CFG
                            if prev_ins.split(' ')[2] == edge[0][1]:
                                if state_simulation.is_real(path_constraint):
                                    if path_constraint != 1:
                                        print('[PATH CONS]: %s not go true way' % tag)
                                        go_true = False
                                else:
                                    constraint = simplify(path_constraint == 1)
                                    # if isinstance(path_constraint, z3.z3.BoolRef):
                                    #     constraint = path_constraint
                                    # else:
                                    #     constraint = BitVec(path_constraint, 256) == 1
                                    # print('[CONS==1]:', type(constraint), constraint)
                                    # path_cons_1.add(constraint)
                                    path_cons_1.assert_and_track(constraint, pc_track_1.get_pc_var())
                                    # constraint = str(path_constraint).replace('&', '\n&').replace(',', ',\n')
                                    edges[index] = edge_add_path_constraint(edge, constraint)
                            else:
                                if state_simulation.is_real(path_constraint):
                                    if path_constraint != 0:
                                        print('[PATH CONS]: %s not go False way' % tag)
                                        go_false = False
                                else:
                                    constraint = simplify(path_constraint == 0)
                                    # if isinstance(path_constraint, z3.z3.BoolRef):
                                    #     constraint = Not(path_constraint)
                                    # else:
                                    #     constraint = BitVec(path_constraint, 256) == 0
                                    # print('[CONS==0]:', type(constraint), constraint)
                                    # path_cons_2.add(constraint)
                                    path_cons_2.assert_and_track(constraint, pc_track_2.get_pc_var())
                                    # constraint = str(constraint).replace('&', '\n&').replace(',', ',\n')
                                    edges[index] = edge_add_path_constraint(edge, constraint)

                    # NOTE: run two path
                    state_1 = dict()
                    for key, val in state.items():
                        in_new_state = dict()
                        for key1, val1 in val.items():
                            in_new_state[key1] = val1
                        state_1[key] = in_new_state

                    state_2 = dict()
                    for key, val in state.items():
                        in_new_state = dict()
                        for key1, val1 in val.items():
                            in_new_state[key1] = val1
                        state_2[key] = in_new_state

                    if is_expr(gas):
                        gas_1 = gas
                        gas_2 = gas
                    else:
                        gas_1 = copy.deepcopy(gas)
                        gas_2 = copy.deepcopy(gas)
                    tag_1 = copy.deepcopy(tag)
                    tag_2 = copy.deepcopy(tag)
                    has_jump_in_1 = copy.deepcopy(has_jump_in)
                    has_jump_in_2 = copy.deepcopy(has_jump_in)
                    jump_in_num_1 = copy.deepcopy(jump_in_num)
                    jump_in_num_2 = copy.deepcopy(jump_in_num)
                    path_label_1 = path_label * prime_list.pop(0)
                    path_label_2 = path_label * prime_list.pop(0)

                    if prev_ins.split(' ')[2] == first_tag:
                        if go_true:
                            symbolic_implement(state_1, gas_1, path_cons_1,
                                               first_tag, tag_1, tag_stack_first,
                                               has_jump_in_1, jump_in_num_1, path_label_1, pc_track_1)
                        if go_false:
                            symbolic_implement(state_2, gas_2, path_cons_2,
                                               second_tag, tag_2, tag_stack_second,
                                               has_jump_in_2, jump_in_num_2, path_label_2, pc_track_2)
                        return
                    else:
                        if go_true:
                            symbolic_implement(state_2, gas_2, path_cons_2,
                                               second_tag, tag_2, tag_stack_second,
                                               has_jump_in_2, jump_in_num_2, path_label_2, pc_track_2)
                        if go_false:
                            symbolic_implement(state_1, gas_1, path_cons_1,
                                               first_tag, tag_1, tag_stack_first,
                                               has_jump_in_1, jump_in_num_1, path_label_1, pc_track_1)
                        return
                elif opcode in ['STOP', 'RETURN', 'REVERT', 'INVALID']:
                    '''
                    STOP, RETURN, REVERT, INVALID:
                    the final node of the path
                    '''

                    # NOTE: update gas of the node on CFG
                    node = node_add_gas(node, node_gas)
                    node = node_add_path_gas_sum(node, gas)

                    # NOTE: Add the state to the node on CFG
                    node, convergence = node_add_state(node, state, path_label, tag)

                    # NOTE: if the state is same with previous one, then it's convergence --> stop
                    # if convergence:
                    #     return

                    count_path += 1

                    if is_expr(gas):
                        gas_cons = gas <= 21000
                        path_cons.assert_and_track(gas_cons, 'gas_cons')
                        # pc_var = get_solver_var(path_cons)

                        print('[INFO] Checking Satisfiability of Path Constraints with %s pc...' % len(path_cons.assertions()))
                        if path_cons.check() == sat:
                            print('[INFO] Path Constraints: sat')
                            ans = path_cons.model()
                            print('[INFO] model:', len(ans), 'variables\n', ans)
                            new_pc_gas = {'path_constraints': path_cons, 'ans': ans, 'gas': gas}
                            global_vars.add_pc_gas(new_pc_gas)
                        else:
                            print('[INFO] Path Constraints: unsat')
                            unsat_core = path_cons.unsat_core()
                            print('[INFO] Conflict: %s' % unsat_core)

                    return
                elif line == 'Stack Sum':
                    '''
                    if there isn't any JUMP or JUMPI, there is one way to go,
                    so find the next node in edges and go to there 
                    '''

                    # NOTE: update gas of the node on CFG
                    node = node_add_gas(node, node_gas)

                    # NOTE: Add the state to the node on CFG
                    new_state = dict()
                    for key, val in state.items():
                        in_new_state = dict()
                        for key1, val1 in val.items():
                            in_new_state[key1] = val1
                        new_state[key] = in_new_state
                    node, convergence = node_add_state(node, new_state, path_label, tag)

                    # NOTE: if the state is same with previous one, then it's convergence --> stop
                    if convergence:
                        return

                    for index, edge in enumerate(edges):
                        if edge[0][0] == tag:
                            edges[index] = edge_change_color(edge)
                            next_tag = edge[0][1]
                            tag_stack.append(next_tag)
                            return symbolic_implement(state, gas, path_cons,
                                                      next_tag, tag, tag_stack,
                                                      has_jump_in, jump_in_num, path_label, pc_track)
                    return
                else:

                    # NOTE: stack simulation
                    state, ins_gas, path_constraint = state_simulation.state_simulation(opcode, state)
                    if is_expr(gas):
                        gas = simplify(gas + ins_gas)
                    else:
                        gas = gas + ins_gas
                    if is_expr(node_gas):
                        node_gas = simplify(node_gas + ins_gas)
                    else:
                        node_gas = node_gas + ins_gas

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
    label = edge[1]['label']
    retval = list()
    retval.append(edge_set)
    if color == 'blue':
        retval.append({'label': label, 'color': 'green'})
    elif color == 'green':
        retval.append({'label': label, 'color': 'purple'})
    elif color == 'purple':
        retval.append({'label': label, 'color': 'red'})
    else:
        retval.append({'label': label, 'color': 'black'})
    return tuple(retval)


def node_add_gas(node, gas):
    if 'Gas: ' not in node[1]['label']:
        node[1]['label'] += '\nGas: %s' % str(gas)
    return node


def node_add_path_gas_sum(node, gas):
    node[1]['label'] += '\n'
    if 'State:' in node[1]['label']:
        state_position = node[1]['label'].find('State')
        first_part = node[1]['label'][:state_position-1]
        second_part = node[1]['label'][state_position:]

        if 'Path Gas Sum:' in first_part:
            first_part = first_part[:-2]
            first_part += ', %s]' % str(gas)
        else:
            first_part += '\nPath Gas Sum:\n[%s]' % str(gas)
        node[1]['label'] = '%s\n\n%s' % (first_part, second_part)
    else:
        if 'Path Gas Sum:' in node[1]['label']:
            node[1]['label'] = node[1]['label'][:-2]
            node[1]['label'] += ',\n%s]' % str(gas)
        else:
            node[1]['label'] += '\nPath Gas Sum:\n[%s]' % str(gas)
    return node


def edge_add_path_constraint(edge, constraint):
    if 'Path Constraint:' in edge[1]['label']:
        edge[1]['label'] = edge[1]['label'][:-1]
        edge[1]['label'] += ',\n%s]' % str(constraint)
    else:
        edge[1]['label'] += 'Path Constraint:\n[%s]' % str(constraint)

    color = edge[1]['color']
    if color == 'blue':
        edge[1]['color'] = 'brown'
    return edge


def node_add_state(node, state, path_label, tag):
    global prime_check_list

    in_stack = state['Stack']
    in_memory = state['Memory']
    in_storage = state['Storage']
    same_state = False

    for key in in_stack:
        if not isinstance(in_stack[key], str):
            in_stack[key] = str(in_stack[key])
    for key in in_memory:
        if not isinstance(in_memory[key], str):
            in_memory[key] = str(in_memory[key])
    for key in in_storage:
        if not isinstance(in_storage[key], str):
            in_storage[key] = str(in_storage[key])

    if 'State:' in node[1]['label']:
        state_position = node[1]['label'].find('State:') + 7
        state_str = node[1]['label'][state_position:].replace(',\n', ',')
        state_json = json.loads(state_str)

        curr_path_prime_list = []
        for item in prime_check_list:
            if path_label % item == 0:
                curr_path_prime_list.append(item)

        new_path = True
        for index, val in enumerate(state_json):
            state_path_label = val[-1]['Path Label']
            position_prime_list = []
            for item in prime_check_list:
                if state_path_label % item == 0:
                    position_prime_list.append(item)
            for item in curr_path_prime_list:
                if item in position_prime_list:
                    new_path = False
                    if val[-1]['Stack'] == in_stack and val[-1]['Memory'] == in_memory and val[-1]['Storage'] == in_storage:
                        same_state = True
                        # print('[TAG SAME]:', tag)
                    else:
                        # print('[TAG NOT SAME]:', tag)
                        # if val[-1]['Stack'] != in_stack:
                        #     print('\n[STACK]:', False, tag, val[-1]['Stack'], in_stack)
                        # if val[-1]['Memory'] != in_memory:
                        #     print('\n[MEM]:', False, tag, val[-1]['Memory'], in_memory)
                        # if val[-1]['Storage'] != in_storage:
                        #     print('\n[STO]:', False, tag, val[-1]['Storage'], in_storage)

                        state_json[index].append({'Path Label': path_label, 'Stack': in_stack, 'Memory': in_memory, 'Storage': in_storage})
        if new_path:
            state_json.append([{'Path Label': path_label, 'Stack': in_stack, 'Memory': in_memory, 'Storage': in_storage}])

        node[1]['label'] = node[1]['label'][:state_position-7]
        state_str = json.dumps(state_json)
        state_str = state_str.replace(',', ',\n', 2)
        node[1]['label'] += state_str
    else:
        state_json = [[{'Path Label': path_label, 'Stack': in_stack, 'Memory': in_memory, 'Storage': in_storage}]]
        state_str = json.dumps(state_json)
        state_str = state_str.replace(',', ',\n', 2)
        node[1]['label'] += '\n\nState:\n%s' % state_str
    return node, same_state

