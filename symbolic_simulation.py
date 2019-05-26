from gas_price import *
from z3 import *
from var_generator import *
from z3_func import *
from global_constants import *
import json
import state_simulation
import copy
import global_vars
import loop_detection

count_sim = 0
# stack = []
storage = []
memory = []
nodes = []
edges = []
count_path = 0
constant_path = 0
bounded_path = 0
unbounded_path = 0
tag_run_time = dict()
tag_gas_sum = dict()
final_gas_sum = dict()
prime_list = []
prime_check_list = []
LT_condition = None


def symbolic_simulation(nodes_in, edges_in):
    global nodes
    global edges
    global count_path
    global constant_path
    global bounded_path
    global unbounded_path
    global tag_run_time
    global prime_list
    global prime_check_list
    global final_gas_sum

    nodes = nodes_in
    edges = edges_in

    count_path = 0
    constant_path = 0
    bounded_path = 0
    unbounded_path = 0
    tag_run_time = dict()
    count_loop = dict()
    state = {'Stack': {}, 'Memory': {}, 'Storage': {}}
    gas = 0
    path_cons = Solver()
    gas_cons = Solver()
    path_cons.set(unsat_core=True)
    pc_track = SolverUnsatCore()
    loop_condition = dict()
    symbolic_implement(state, gas, path_cons, gas_cons,
                       '0', [], count_loop,
                       pc_track, loop_condition)
    print('\n[INFO] Find %s path: %s constant path, %s bounded path, and %s unbounded path.' %
          (count_path, constant_path, bounded_path, unbounded_path))
    print('[INFO] Vulnerability Path:', global_vars.get_sat_path_count())
    return nodes, edges


def symbolic_implement(state, gas, path_cons, gas_cons,
                       tag, path_tag, count_loop,
                       pc_track, loop_condition):
    # print('[TAG]:', tag)
    """
    param:
    [state]: the state of 'Stack', 'Memory', and 'Storage'
    [gas]: the sum of the gas consumption to current node
    [path_cons]: path constraints
    [gas_cons]: gas constraints
    [tag]: the tag of the node to run the symbolic simulation
    [path_tag]: a list of tag of executed path
    [pc_track]: track the path constraint for z3
    [loop_condition]: last JUMPI condition in order to calculate the loop condit\textbf{nodes}T\textbf{nodion
    """
    # global stack
    global nodes
    global edges
    global count_path
    global constant_path
    global bounded_path
    global unbounded_path
    global tag_run_time
    global prime_list
    global LT_condition

    prev_ins = ''
    prev_jumpi_ins = dict()

    for node in nodes:
        if node[0] == tag:
            # node_gas = [0, '']
            node_gas = 0

            label = node[1].get('label')
            # NOTE: remove 'TAG' in label ([0, 1])
            ins_list = label.split('\n')[2:]

            for ins in ins_list:
                ins_set = ins.split(': ')
                line = ins_set[0]
                opcode = ins_set[1]

                # if tag in ['121']:
                #     print('[STACK]:', tag, ins, state['Stack'])
                #     print('[MEM]:', state['Memory'])
                #     print('[STO]:', state['Storage'])
                #     print('[GAS]:', gas, '\n')

                if isinstance(gas, z3.z3.IntNumRef):
                    gas = gas.as_long()

                if opcode.split(' ')[0] == 'tag':
                    pass
                elif opcode in ['JUMP', 'JUMP [in]']:

                    # NOTE: add tag to path tag
                    path_tag.append(tag)

                    # NOTE: stack simulation
                    state, ins_gas, path_constraint, gas_constraint, var_constraint, prev_jumpi_ins, next_jump_tag = \
                        state_simulation.state_simulation(opcode, state, line, prev_jumpi_ins)

                    if is_expr(gas_constraint):
                        gas_cons.add(gas_constraint)

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

                    # NOTE: Add the state to the node on CFG
                    new_state = dict()
                    for key, val in state.items():
                        in_new_state = dict()
                        for key1, val1 in val.items():
                            in_new_state[key1] = val1
                        new_state[key] = in_new_state
                    node, loop_gas = node_add_state(node, new_state, path_tag, tag, gas)

                    # NOTE: JUMP to next tag
                    edge_exist = False
                    for index, edge in enumerate(edges):
                        if edge[0][0] == tag and edge[0][1] == next_jump_tag:
                            edges[index] = edge_change_color(edge)
                            edge_exist = True
                            break
                    if not edge_exist:
                        edges.append(((str(tag), next_jump_tag), {'label': '', 'color': 'blue'}))

                    return symbolic_implement(state, gas, path_cons, gas_cons,
                                              next_jump_tag, path_tag, count_loop,
                                              pc_track, loop_condition)
                elif opcode == 'JUMP [out]':
                    # NOTE: add tag to path tag
                    path_tag.append(tag)

                    # NOTE: stack simulation
                    state, ins_gas, path_constraint, gas_constraint, var_constraint, prev_jumpi_ins, next_jump_tag = \
                        state_simulation.state_simulation(opcode, state, line, prev_jumpi_ins)

                    if is_expr(gas_constraint):
                        gas_cons.add(gas_constraint)

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
                    # node = node_add_path_gas_sum(node, gas)

                    # NOTE: Add the state to the node on CFG
                    new_state = dict()
                    for key, val in state.items():
                        in_new_state = dict()
                        for key1, val1 in val.items():
                            in_new_state[key1] = val1
                        new_state[key] = in_new_state
                    node, loop_gas = node_add_state(node, new_state, path_tag, tag, gas)

                    # NOTE: JUMP to next tag
                    edge_exist = False
                    for index, edge in enumerate(edges):
                        if edge[0][0] == tag and edge[0][1] == next_jump_tag:
                            edges[index] = edge_change_color(edge)
                            edge_exist = True
                            break
                    if not edge_exist:
                        edges.append(((str(tag), next_jump_tag), {'label': '', 'color': 'blue'}))

                    return symbolic_implement(state, gas, path_cons, gas_cons,
                                              next_jump_tag, path_tag, count_loop,
                                              pc_track, loop_condition)
                elif opcode == 'JUMPI':
                    next_false_tag = None
                    # next_true_tag = None
                    go_true = True
                    go_false = True
                    pop_pc = None
                    try:
                        path_cons_true = path_cons.translate(main_ctx())
                        path_cons_false = path_cons.translate(main_ctx())
                    except z3.z3types.Z3Exception:
                        pop_pc = path_cons.assertions()[len(path_cons.assertions())-1]
                        path_cons.pop()
                        path_cons_true = path_cons.translate(main_ctx())
                        path_cons_false = path_cons.translate(main_ctx())
                    pc_track_true = SolverUnsatCore()
                    pc_track_true.set_count(pc_track.get_count())
                    pc_track_false = SolverUnsatCore()
                    pc_track_false.set_count(pc_track.get_count())
                    loop_pc = None

                    # NOTE: add tag to path tag
                    path_tag.append(tag)

                    # NOTE: stack simulation
                    state, ins_gas, path_constraint, gas_constraint, var_constraint, prev_jumpi_ins, next_true_tag = \
                        state_simulation.state_simulation(opcode, state, line, prev_jumpi_ins)

                    if is_expr(gas_constraint):
                        gas_cons.add(gas_constraint)

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
                    # node = node_add_path_gas_sum(node, gas)

                    # NOTE: Add the state to the node on CFG
                    new_state = dict()
                    for key, val in state.items():
                        in_new_state = dict()
                        for key1, val1 in val.items():
                            in_new_state[key1] = val1
                        new_state[key] = in_new_state
                    node, loop_gas = node_add_state(node, new_state, path_tag, tag, gas)

                    # NOTE: Loop Detection
                    if LOOP_DETECTION:
                        if tag not in loop_condition.keys():
                            loop_condition[tag] = None
                        has_loop, cons_val = loop_detection.loop_detection(prev_jumpi_ins, loop_condition[tag])
                    else:
                        if tag not in count_loop.keys():
                            count_loop[tag] = 0
                        if count_loop[tag] == 10:
                            return
                        else:
                            count_loop[tag] += 1
                            has_loop = False
                            cons_val = None
                            if tag == '25':
                                print('[LOOP PC - %s]: [TAG %s]' % (count_loop[tag], tag), path_constraint)
                    if has_loop:
                        new_var = BitVec(global_vars.get_gen().gen_loop_var(tag), 256)
                        gas_cons.add(state_simulation.add_gas_constraint(new_var, UNSIGNED_BOUND_NUMBER))
                        loop_pc = loop_detection.handle_loop_condition(prev_jumpi_ins, loop_condition, tag,
                                                                       cons_val, new_var)
                        # if prev_jumpi_ins['ins'] == 'ISZERO':
                        #     sym_var = cons_val['var']
                        #     gas_cons.add(state_simulation.add_gas_constraint(sym_var, UNSIGNED_BOUND_NUMBER))
                        #     if str(cons_val['op']) == 'ULT':
                        #         if cons_val['var_position'] == 1:
                        #             loop_pc = simplify(If(Not(ULT(sym_var, cons_val['diff'] * new_var)), 1, 0))
                        #         else:
                        #             loop_pc = simplify(If(Not(ULT(cons_val['diff'] * new_var, sym_var)), 1, 0))
                        #     elif str(cons_val['op']) == 'UGT':
                        #         if cons_val['var_position'] == 1:
                        #             loop_pc = simplify(If(Not(UGT(sym_var, cons_val['diff'] * new_var)), 1, 0))
                        #         else:
                        #             loop_pc = simplify(If(Not(UGT(cons_val['diff'] * new_var, sym_var)), 1, 0))
                        #     elif str(cons_val['op']) == 'ULE':
                        #         if cons_val['var_position'] == 1:
                        #             loop_pc = simplify(If(Not(ULE(sym_var, cons_val['diff'] * new_var)), 1, 0))
                        #         else:
                        #             loop_pc = simplify(If(Not(ULE(cons_val['diff'] * new_var, sym_var)), 1, 0))
                        #     else:
                        #         print('[LOOp ERROR]:', cons_val)
                        #         raise ValueError('LOOP INS ERROR - 329')
                        # elif prev_jumpi_ins['ins'] in ['LT', 'EQ', 'GT']:
                        #     if is_expr(prev_jumpi_ins['s1']) and prev_jumpi_ins['s1'] == loop_condition[tag]['s1']:
                        #         sym_var = prev_jumpi_ins['s1']
                        #         var_position = 1
                        #     elif is_expr(prev_jumpi_ins['s2']) and prev_jumpi_ins['s2'] == loop_condition[tag]['s2']:
                        #         sym_var = prev_jumpi_ins['s2']
                        #         var_position = 2
                        #     else:
                        #         raise ValueError('LOOP SYM VAR ERROR - 328')
                        #
                        #     if prev_jumpi_ins['ins'] == 'LT':
                        #         if var_position == 1:
                        #             loop_pc = simplify(If(ULT(sym_var, cons_val['diff'] * new_var), 1, 0))
                        #         else:
                        #             loop_pc = simplify(If(ULT(cons_val['diff'] * new_var, sym_var), 1, 0))
                        #     elif prev_jumpi_ins['ins'] == 'GT':
                        #         if var_position == 1:
                        #             loop_pc = simplify(If(UGT(sym_var, cons_val['diff'] * new_var), 1, 0))
                        #         else:
                        #             loop_pc = simplify(If(UGT(cons_val['diff'] * new_var, sym_var), 1, 0))
                        #     elif prev_jumpi_ins['ins'] == 'EQ':
                        #         loop_pc = simplify(If(cons_val['diff'] * new_var == sym_var, 1, 0))
                        #     else:
                        #         raise ValueError('LOOP INS ERROR - 339')
                        # else:
                        #     sym_var = BitVec(cons_val['var'], 256)
                        #     gas_cons.add(state_simulation.add_gas_constraint(sym_var, UNSIGNED_BOUND_NUMBER))
                        #     if cons_val['op'] == 'ULT':
                        #         if cons_val['var_position'] == 1:
                        #             loop_pc = simplify(If(ULT(sym_var, cons_val['diff'] * new_var),1 , 0))
                        #         else:
                        #             loop_pc = simplify(If(ULT(cons_val['diff'] * new_var, sym_var), 1, 0))
                        #     else:
                        #         raise ValueError('LOOP INS ERROR - 329')
                        loop_gas_var = simplify(loop_gas * BV2Int(new_var))
                        gas += loop_gas_var
                    else:
                        loop_condition[tag] = prev_jumpi_ins
                    prev_jumpi_ins = dict()

                    # NOTE: Find next jump tag and add constraint to the edge
                    for index, edge in enumerate(edges):
                        if edge[0][0] == tag and edge[0][1] == next_true_tag:
                            if loop_pc is None:
                                if pop_pc is not None:
                                    path_cons_true.add(pop_pc)
                                if is_expr(path_constraint):
                                    constraint = simplify(path_constraint == 1)
                                    if constraint not in path_cons_true.assertions():
                                        path_cons_true.push()
                                        path_cons_true.add(constraint)
                                else:
                                    constraint = path_constraint == 1
                                edges[index] = edge_add_path_constraint(edge, constraint)
                            else:
                                constraint = simplify(loop_pc == 1)
                                path_cons_true.add(constraint)
                                edges[index] = edge_change_loop_constraint(edge, constraint)
                        elif edge[0][0] == tag and edge[0][1] != next_true_tag:
                            next_false_tag = edge[0][1]
                            if loop_pc is None:
                                if pop_pc is not None:
                                    path_cons_false.add(pop_pc)
                                if is_expr(path_constraint):
                                    constraint = simplify(path_constraint == 0)
                                    if constraint not in path_cons_false.assertions():
                                        path_cons_false.push()
                                        path_cons_false.add(constraint)
                                else:
                                    constraint = path_constraint == 0
                                edges[index] = edge_add_path_constraint(edge, constraint)
                            else:
                                constraint = simplify(loop_pc == 0)
                                path_cons_false.add(constraint)
                                edges[index] = edge_change_loop_constraint(edge, constraint)

                    # NOTE: Determine run the path or not
                    if isinstance(path_constraint, int):
                        if path_constraint == 1:
                            go_true = True
                            go_false = False
                        elif path_constraint == 0:
                            go_true = False
                            go_false = True
                        else:
                            raise ValueError('JUMPI constraint error')

                    # NOTE: Create params of two paths
                    state_true = dict()
                    for key, val in state.items():
                        in_new_state = dict()
                        for key1, val1 in val.items():
                            in_new_state[key1] = val1
                        state_true[key] = in_new_state
                    state_false = dict()
                    for key, val in state.items():
                        in_new_state = dict()
                        for key1, val1 in val.items():
                            in_new_state[key1] = val1
                        state_false[key] = in_new_state

                    if is_expr(gas):
                        gas_true = gas
                        gas_false = gas
                    else:
                        gas_true = copy.deepcopy(gas)
                        gas_false = copy.deepcopy(gas)
                    path_tag_true = copy.deepcopy(path_tag)
                    path_tag_false = copy.deepcopy(path_tag)
                    gas_cons_true = gas_cons.translate(main_ctx())
                    gas_cons_false = gas_cons.translate(main_ctx())
                    count_loop_true = copy.deepcopy(count_loop)
                    count_loop_false = copy.deepcopy(count_loop)

                    loop_condition_true = dict()
                    loop_condition_false = dict()
                    for idx, val in loop_condition.items():
                        loop_condition_true[idx] = val
                        loop_condition_false[idx] = val

                    # NOTE: Execute the path
                    if has_loop:
                        if next_true_tag in path_tag:
                            return symbolic_implement(state_false, gas_false, path_cons_false, gas_cons_false,
                                                      next_false_tag, path_tag_false, count_loop_false,
                                                      pc_track_false, loop_condition_false)
                        else:
                            return symbolic_implement(state_true, gas_true, path_cons_true, gas_cons_true,
                                                      next_true_tag, path_tag_true, count_loop_true,
                                                      pc_track_true, loop_condition_true)
                    else:
                        if go_true:
                            symbolic_implement(state_true, gas_true, path_cons_true, gas_cons_true,
                                               next_true_tag, path_tag_true, count_loop_true,
                                               pc_track_true, loop_condition_true)
                        if go_false:
                            symbolic_implement(state_false, gas_false, path_cons_false, gas_cons_false,
                                               next_false_tag, path_tag_false, count_loop_false,
                                               pc_track_false, loop_condition_false)
                        return
                elif opcode in ['STOP', 'RETURN', 'REVERT', 'INVALID']:
                    # NOTE: add gas sum to final_gas_sum
                    global_vars.add_final_gas(tag, gas)

                    # NOTE: add tag to path tag
                    path_tag.append(tag)

                    # NOTE: update gas of the node on CFG
                    node = node_add_gas(node, node_gas)
                    # node = node_add_path_gas_sum(node, gas)

                    # NOTE: Add the state to the node on CFG
                    node_add_state(node, state, path_tag, tag, gas)

                    count_path += 1
                    global_vars.add_total_path_count()

                    for gc in gas_cons.assertions():
                        path_cons.add(gc)
                    # print('[PC]:', tag, path_cons)
                    # print('[INFO] Checking Satisfiability of Path Constraints on tag %s with %s pc...'
                    #       % (tag, len(path_cons.assertions())))

                    if path_cons.check() == sat:
                        if is_expr(gas) and not isinstance(gas, z3.z3.IntNumRef):
                            if 'loop' in str(gas):
                                unbounded_path += 1
                            else:
                                bounded_path += 1

                            gas_cons = global_vars.get_gas_limit() < gas
                            # path_cons.assert_and_track(gas_cons, 'gas_cons')
                            path_cons.add(gas_cons)
                            # pc_var = get_solver_var(path_cons)
                            if path_cons.check() == sat:
                                print('[INFO] Path Constraints: sat')
                                global_vars.add_sat_path_count()
                                ans = path_cons.model()
                                # print('[INFO] model:', len(ans), 'variables')
                                new_pc_gas = {'path_constraints': path_cons, 'ans': ans, 'gas': gas, 'tags': path_tag}
                                global_vars.add_pc_gas(new_pc_gas)
                            # else:
                            #     print('[INFO] Path Constraints: unsat')
                            #     unsat_core = path_cons.unsat_core()
                            #     print('[INFO] Conflict: %s' % unsat_core)
                        else:
                            constant_path += 1
                            if isinstance(gas, z3.z3.IntNumRef):
                                gas = gas.as_long()
                            if gas > global_vars.get_gas_limit() and path_cons.check() == sat:
                                print('[INFO] Path Constraints: sat')
                                global_vars.add_sat_path_count()
                                ans = path_cons.model()
                                new_pc_gas = {'path_constraints': path_cons, 'ans': ans, 'gas': gas, 'tags': path_tag}
                                global_vars.add_pc_gas(new_pc_gas)

                    return
                elif line == 'Stack Sum':
                    '''
                    if there isn't any JUMP or JUMPI, there is one way to go,
                    so find the next node in edges and go to there 
                    '''
                    # NOTE: add tag to path tag
                    path_tag.append(tag)

                    # NOTE: update gas of the node on CFG
                    node = node_add_gas(node, node_gas)
                    # node = node_add_path_gas_sum(node, gas)

                    # NOTE: Add the state to the node on CFG
                    new_state = dict()
                    for key, val in state.items():
                        in_new_state = dict()
                        for key1, val1 in val.items():
                            in_new_state[key1] = val1
                        new_state[key] = in_new_state
                    node, loop_gas = node_add_state(node, new_state, path_tag, tag, gas)

                    for index, edge in enumerate(edges):
                        if edge[0][0] == tag:
                            edges[index] = edge_change_color(edge)
                            next_tag = edge[0][1]
                            return symbolic_implement(state, gas, path_cons, gas_cons,
                                                      next_tag, path_tag, count_loop,
                                                      pc_track, loop_condition)
                    return
                else:
                    # NOTE: stack simulation
                    state, ins_gas, path_constraint, gas_constraint, var_constraint, prev_jumpi_ins, _ = \
                        state_simulation.state_simulation(opcode, state, line, prev_jumpi_ins)

                    if state is None:
                        return

                    if is_expr(gas_constraint):
                        gas_cons.add(gas_constraint)

                    if is_expr(var_constraint):
                        gas_cons.add(var_constraint)

                    if is_expr(gas):
                        gas = simplify(gas + ins_gas)
                    else:
                        gas = gas + ins_gas
                    if is_expr(node_gas):
                        node_gas = simplify(node_gas + ins_gas)
                    else:
                        node_gas = node_gas + ins_gas
                if 's1' not in prev_jumpi_ins.keys():
                    prev_jumpi_ins['ins'] = prev_ins
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
        state_position = node[1]['label'].find('Path Gas Sum:')

        if state_position != -1:
            first_part = node[1]['label'][:state_position-1]
            second_part = node[1]['label'][state_position:]

            first_part = first_part[:-2]
            first_part += ', %s]' % str(gas)
            node[1]['label'] = '%s\n\n%s' % (first_part, second_part)
        else:
            node[1]['label'] += '\nPath Gas Sum:\n[%s]' % str(gas)
    else:
        if 'Path Gas Sum:' in node[1]['label']:
            node[1]['label'] = node[1]['label'][:-2]
            node[1]['label'] += ',\n%s]' % str(gas)
        else:
            node[1]['label'] += '\nPath Gas Sum:\n[%s]' % str(gas)
    return node


def edge_add_path_constraint(edge, constraint):
    if 'Path Constraint:' in edge[1]['label']:
        edge_split = edge[1]['label'].split('Path Constraint:\n')
        pc = edge_split[1]
        pc_list = json.loads(pc)
        pc_list.append(str(constraint))
        edge[1]['label'] = 'Path Constraint:\n' + json.dumps(pc_list)
    else:
        edge[1]['label'] += 'Path Constraint:\n'
        pc_list = list()
        pc_list.append(str(constraint))
        edge[1]['label'] += json.dumps(pc_list)

    color = edge[1]['color']
    if color == 'blue':
        edge[1]['color'] = 'brown'
    return edge


def edge_change_loop_constraint(edge, constraint):
    edge_split = edge[1]['label'].split('Path Constraint:\n')
    pc = edge_split[1]
    pc_list = json.loads(pc)
    pc_list.pop()
    pc_list.append(str(constraint))
    edge[1]['label'] = 'Path Constraint:\n' + json.dumps(pc_list)
    return edge


def node_add_state(node, state, path_label, tag, gas):
    global prime_check_list
    global tag_run_time
    global tag_gas_sum

    in_stack = state['Stack']
    in_memory = state['Memory']
    in_storage = state['Storage']
    loop_gas = 0

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

        new_path = True
        if path_label.count(path_label[-1]) > 1:
            first_idx = path_label.index(path_label[-1])
            curr_tag = path_label[:first_idx]

            for index, val in enumerate(state_json):
                state_path_label = val[-1]['Path Label']
                state_trueag = state_path_label[:first_idx]

                if curr_tag == state_trueag:
                    new_path = False

                    gas_sum = tag_gas_sum[tag]
                    loop_gas = gas - gas_sum
                    break

        if new_path:
            state_json.append([{'Path Label': path_label, 'Stack': in_stack, 'Memory': in_memory, 'Storage': in_storage}])

        node[1]['label'] = node[1]['label'][:state_position]
        state_str = json.dumps(state_json).replace('\n', '').replace(',', ',\n', 2)\
            .replace(', "Stack":', ',\n\n"Stack":').replace(', "Memory"', ',\n"Memory"')\
            .replace(', "Storage"', ',\n"Storage"').replace('", "', '",\n"')
        node[1]['label'] += state_str
    else:
        tag_gas_sum.update({tag: gas})
        state_json = [[{'Path Label': path_label, 'Stack': in_stack, 'Memory': in_memory, 'Storage': in_storage}]]
        state_str = json.dumps(state_json)
        state_str = state_str.replace(',', ',\n', 2)
        node[1]['label'] += '\n\nState:\n%s' % state_str
    return node, loop_gas
