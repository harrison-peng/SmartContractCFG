from gas_price import *
from z3_func import *
from global_constants import *
import state_simulation as state_simulation
import copy
import global_vars
import loop_detection

count_sim = 0
storage = []
memory = []
nodes = []
edges = []
count_path = 0
constant_path = 0
bounded_path = 0
unbounded_path = 0
addr_run_time = dict()
addr_gas_sum = dict()
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
    global addr_run_time
    global prime_list
    global prime_check_list
    global final_gas_sum

    nodes = nodes_in
    edges = edges_in

    count_path = 0
    constant_path = 0
    bounded_path = 0
    unbounded_path = 0
    addr_run_time = dict()
    count_loop = dict()
    state = {'Stack': {}, 'Memory': {}, 'Storage': {}}
    gas = 0
    path_cons = Solver()
    gas_cons = Solver()
    loop_condition = dict()
    symbolic_implement(state, gas, path_cons, gas_cons,
                       0, [], count_loop, loop_condition)

    for up in global_vars.get_unbounded_pc_gas():
        for bp in global_vars.get_bounded_pc_gas():
            if up['path'] == bp['path']:
                global_vars.del_bounded_pc_gas(bp)
                count_path -= 1
                if bp['type'] == 'bounded':
                    bounded_path -= 1
                else:
                    constant_path -= 1
                break

    global_vars.set_constant_path_count(constant_path)
    global_vars.set_bounded_path_count(bounded_path)
    global_vars.set_unbounded_path_count(unbounded_path)
    global_vars.set_total_path_count(count_path)
    global_vars.set_sat_path_count(len(global_vars.get_unbounded_pc_gas()) + len(global_vars.get_bounded_pc_gas()))
    print('\n[INFO] Find %s path: %s constant path, %s bounded path, and %s unbounded path.' %
          (count_path, constant_path, bounded_path, unbounded_path))
    print('[INFO] Vulnerability Path:', global_vars.get_sat_path_count())
    return nodes, edges


def symbolic_implement(state, gas, path_cons, gas_cons,
                       addr, path_addr, count_loop, loop_condition):
    # print('[addr]:', addr)
    """
    param:
    [state]: the state of 'Stack', 'Memory', and 'Storage'
    [gas]: the sum of the gas consumption to current node
    [path_cons]: path constraints
    [gas_cons]: gas constraints
    [addr]: the addr of the node to run the symbolic simulation
    [path_addr]: a list of addr of executed path
    [loop_condition]: last JUMPI condition in order to calculate the loop condit\textbf{nodes}T\textbf{nodion
    """
    global nodes
    global edges
    global count_path
    global constant_path
    global bounded_path
    global unbounded_path
    global addr_run_time
    global prime_list
    global LT_condition

    prev_ins = ''
    prev_jumpi_ins = dict()

    for node in nodes:
        if node['addr'] == addr:
            node_gas = 0
            ins_list = node['ins']

            for ins in ins_list:
                ins_set = ins.split(': ')
                line = ins_set[0]
                opcode = ins_set[1]

                # if addr in [192]:
                #     print('[INS]:', ins)
                #     print('[STACK]:', addr, ins, state['Stack'], '\n')
                #     print('[MEM]:', state['Memory'])
                #     print('[STO]:', state['Storage'], '\n')
                #     print('[GAS]:', gas, '\n')

                if isinstance(gas, z3.z3.IntNumRef):
                    gas = gas.as_long()

                if opcode == 'JUMP':
                    # NOTE: add address to path address
                    path_addr.append(addr)

                    # NOTE: stack simulation
                    state, ins_gas, path_constraint, gas_constraint, prev_jumpi_ins, next_jump_addr = \
                        state_simulation.state_simulation(opcode, state, line, prev_jumpi_ins)

                    for c in gas_constraint:
                        if is_expr(c):
                            gas_cons.add(c)

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
                    node, _ = node_add_state(node, new_state, path_addr, addr, gas)

                    # NOTE: JUMP to next addr
                    edge_exist = False
                    for index, edge in enumerate(edges):
                        if edge[0][0] == str(addr) and edge[0][1] == str(next_jump_addr):
                            edges[index] = edge_change_color(edge)
                            edge_exist = True
                            break
                    if not edge_exist:
                        edges.append(((str(addr), str(next_jump_addr)), {'label': '', 'color': 'blue'}))

                    return symbolic_implement(state, gas, path_cons, gas_cons,
                                              next_jump_addr, path_addr, count_loop, loop_condition)
                elif opcode == 'JUMPI':
                    # if addr == 260:
                    #     print('[260]:', state['Stack'])
                    #     print('[mem]:', state['Memory'])
                    #     print('[sto]:', state['Storage'])
                    #     print('[gas]:', gas)
                    next_false_addr = int(line) + 1
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
                    loop_pc = None

                    # NOTE: add address to path address
                    path_addr.append(addr)

                    # NOTE: stack simulation
                    # print('[STACK]:', addr, state['Stack'])
                    state, ins_gas, path_constraint, gas_constraint, prev_jumpi_ins, next_true_addr = \
                        state_simulation.state_simulation(opcode, state, line, prev_jumpi_ins)
                    # print('[JUMPIIIII]:', addr, next_true_addr, simplify(path_constraint), '\n')

                    for c in gas_constraint:
                        if is_expr(c):
                            gas_cons.add(c)

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
                    node, loop_gas = node_add_state(node, new_state, path_addr, addr, gas)

                    # NOTE: Loop Detection
                    if addr not in count_loop.keys():
                        count_loop[addr] = 0
                    count_loop[addr] += 1
                    has_loop = False
                    cons_val = None
                    if LOOP_DETECTION:
                        if addr not in loop_condition.keys():
                            loop_condition[addr] = {'gas': None, 'cons': None}

                        # NOTE: Store gas of first time in the loop
                        if count_loop[addr] == 1:
                            loop_condition[addr]['gas'] = gas

                        # NOTE: detect the loop value in last two times
                        if is_expr(path_constraint) and count_loop[addr] == LOOP_ITERATIONS:
                            cons_val = loop_detection.loop_detection(prev_jumpi_ins, loop_condition[addr]['cons'])
                            has_loop = True
                    else:
                        if count_loop[addr] == LOOP_ITERATIONS:
                            return

                    if has_loop:
                        new_var = BitVec(global_vars.get_gen().gen_loop_var(addr), 256)
                        gas_cons.add(state_simulation.add_gas_constraint(new_var, UNSIGNED_BOUND_NUMBER))
                        loop_pc = loop_detection.handle_loop_condition(prev_jumpi_ins, loop_condition[addr]['cons'],
                                                                       addr, cons_val, new_var)
                        loop_gas_var = simplify(loop_gas * BV2Int(new_var))
                        gas = loop_condition[addr]['gas'] + loop_gas_var

                        addr_idx_1 = path_addr.index(addr)
                        addr_idx_2 = path_addr.index(addr, addr_idx_1 + 1)
                        path_addr = path_addr[:addr_idx_2 + 1]
                    else:
                        loop_condition[addr]['cons'] = prev_jumpi_ins

                    # NOTE: Find next jump addr and add constraint to the edge
                    for idx, edge in enumerate(edges):
                        if edge[0][0] == str(addr):
                            if edge[0][1] == str(next_true_addr):
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
                                    else:
                                        constraint = path_constraint == 1
                                    edges[idx] = edge_add_path_constraint(edge, constraint)
                                else:
                                    constraint = simplify(loop_pc == 1)
                                    path_cons_true.add(constraint)
                                    edges[idx] = edge_change_loop_constraint(edge, constraint)
                            elif edge[0][1] == str(next_false_addr):
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
                                    else:
                                        constraint = path_constraint == 0
                                    edges[idx] = edge_add_path_constraint(edge, constraint)
                                else:
                                    constraint = simplify(loop_pc == 0)
                                    path_cons_false.add(constraint)
                                    edges[idx] = edge_change_loop_constraint(edge, constraint)
                            else:
                                raise ValueError('Edge Error:', edge)

                    # NOTE: Determine run the path or not
                    path_constraint = simplify(path_constraint) if is_expr(path_constraint) else path_constraint
                    path_constraint = path_constraint.as_long() if isinstance(path_constraint, z3.z3.BitVecNumRef) else path_constraint
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
                    path_addr_true = copy.deepcopy(path_addr)
                    path_addr_false = copy.deepcopy(path_addr)
                    gas_cons_true = gas_cons.translate(main_ctx())
                    gas_cons_false = gas_cons.translate(main_ctx())
                    count_loop_true = copy.deepcopy(count_loop)
                    count_loop_false = copy.deepcopy(count_loop)

                    loop_condition_true = dict()
                    loop_condition_false = dict()
                    for idx, val in loop_condition.items():
                        loop_condition_true[idx] = {'gas': val['gas'], 'cons': val['cons']}
                        loop_condition_false[idx] = {'gas': val['gas'], 'cons': val['cons']}

                    # NOTE: Execute the path
                    if has_loop:
                        if next_true_addr in path_addr:
                            return symbolic_implement(state_false, gas_false, path_cons_false, gas_cons_false,
                                                      next_false_addr, path_addr_false, count_loop_false, loop_condition_false)
                        else:
                            return symbolic_implement(state_true, gas_true, path_cons_true, gas_cons_true,
                                                      next_true_addr, path_addr_true, count_loop_true, loop_condition_true)
                    else:
                        if go_true:
                            symbolic_implement(state_true, gas_true, path_cons_true, gas_cons_true,
                                               next_true_addr, path_addr_true, count_loop_true, loop_condition_true)
                        if go_false:
                            symbolic_implement(state_false, gas_false, path_cons_false, gas_cons_false,
                                               next_false_addr, path_addr_false, count_loop_false, loop_condition_false)
                        return
                elif opcode in ['STOP', 'RETURN', 'REVERT', 'INVALID', 'SELFDESTRUCT']:
                    # NOTE: add gas sum to final_gas_sum
                    global_vars.add_final_gas(addr, gas)

                    # NOTE: add addr to path addr
                    path_addr.append(addr)

                    # NOTE: update gas of the node on CFG
                    node = node_add_gas(node, node_gas)

                    # NOTE: Add the state to the node on CFG
                    node_add_state(node, state, path_addr, addr, gas)

                    constraint = Solver()
                    for gc in gas_cons.assertions():
                        constraint.add(simplify(gc))
                    for pc in path_cons.assertions():
                        constraint.add(simplify(pc))
                    # print('[INFO] Checking Satisfiability of Path Constraints on addr %s with %s pc...'
                    #       % (addr, len(path_cons.assertions())))

                    if 'loop' in str(gas):
                        if path_addr not in global_vars.get_executed_unbounded_path():
                            global_vars.add_executed_unbounded_path(path_addr)
                            count_path += 1

                            if constraint.check() == sat:
                                unbounded_path += 1
                                gc = gas >= global_vars.get_gas_limit()
                                constraint.add(simplify(gc))
                                if constraint.check() == sat:
                                    print('[INFO] Path Constraints: sat')
                                    ans = constraint.model()
                                    new_pc_gas = {
                                        'type': 'unbounded',
                                        'path_constraints': constraint,
                                        'model': ans,
                                        'gas': gas,
                                        'path': path_addr
                                    }
                                    global_vars.add_unbounded_pc_gas(new_pc_gas)
                    else:
                        if path_addr not in global_vars.get_executed_bounded_path():
                            global_vars.add_executed_bounded_path(path_addr)
                            count_path += 1

                            if is_expr(gas) and not isinstance(gas, z3.z3.IntNumRef):
                                if constraint.check() == sat:
                                    bounded_path += 1
                                    gc = gas >= global_vars.get_gas_limit()
                                    constraint.add(simplify(gc))
                                    if constraint.check() == sat:
                                        print('[INFO] Path Constraints: sat')
                                        ans = constraint.model()
                                        new_pc_gas = {
                                            'type': 'bounded',
                                            'path_constraints': constraint,
                                            'model': ans,
                                            'gas': gas,
                                            'path': path_addr
                                        }
                                        global_vars.add_bounded_pc_gas(new_pc_gas)
                            else:
                                if constraint.check() == sat:
                                    constant_path += 1
                                    if isinstance(gas, z3.z3.IntNumRef):
                                        gas = gas.as_long()
                                    if gas > global_vars.get_gas_limit():
                                        print('[INFO] Path Constraints: sat')
                                        ans = constraint.model()
                                        new_pc_gas = {
                                            'type': 'constant',
                                            'path_constraints': constraint,
                                            'model': ans,
                                            'gas': gas,
                                            'path': path_addr
                                        }
                                        global_vars.add_bounded_pc_gas(new_pc_gas)
                    return
                else:
                    # NOTE: stack simulation
                    state, ins_gas, path_constraint, gas_constraint, prev_jumpi_ins, _ = \
                        state_simulation.state_simulation(opcode, state, line, prev_jumpi_ins)

                    if state is None:
                        return

                    for c in gas_constraint:
                        if is_expr(c):
                            gas_cons.add(c)

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

            '''
            if there isn't any JUMP or JUMPI, there is one way to go,
            so find the next node in edges and go to there 
            '''
            # NOTE: add addr to path addr
            path_addr.append(addr)

            # NOTE: update gas of the node on CFG
            node = node_add_gas(node, node_gas)

            # NOTE: Add the state to the node on CFG
            new_state = dict()
            for key, val in state.items():
                in_new_state = dict()
                for key1, val1 in val.items():
                    in_new_state[key1] = val1
                new_state[key] = in_new_state
            node, _ = node_add_state(node, new_state, path_addr, addr, gas)

            for index, edge in enumerate(edges):
                if edge[0][0] == str(addr):
                    edges[index] = edge_change_color(edge)
                    next_addr = int(edge[0][1])
                    return symbolic_implement(state, gas, path_cons, gas_cons,
                                              next_addr, path_addr, count_loop, loop_condition)
            return


def edge_change_color(edge):
    edge[1]['color'] = EDGE_COLOR[edge[1]['color']]
    return edge


def node_add_gas(node, gas):
    node['gas'] = gas
    return node


def edge_add_path_constraint(edge, constraint):
    constraint = simplify(constraint) if is_expr(constraint) else constraint
    constraint = str(constraint).replace('\n', '').replace(' ', '')
    if constraint not in edge[1]['label'] and len(constraint) < 2000:
        if len(edge[1]['label']) > 0 and len(constraint) > 20 and len(edge[1]['label'][-1]) > 20:
            prefix_1 = constraint[:20]
            prefix_2 = edge[1]['label'][-1][:20]
            if prefix_1 == prefix_2:
                edge[1]['label'].pop()
        edge[1]['label'].append(constraint)
    color = edge[1]['color']
    constraint_false = not (isinstance(constraint, bool) and constraint is False)
    edge[1]['color'] = 'brown' if color == 'blue' and constraint != 'False' and constraint_false else edge[1]['color']
    return edge


def edge_change_loop_constraint(edge, constraint):
    constraint = simplify(constraint) if is_expr(constraint) else constraint
    constraint = str(constraint).replace('\n', '').replace(' ', '')
    if len(edge[1]['label']) >= 4:
        edge[1]['label'].pop()
        edge[1]['label'].pop()
        edge[1]['label'].pop()
        edge[1]['label'].pop()
    if constraint not in edge[1]['label']:
        edge[1]['label'].append(constraint)
    return edge


def node_add_state(node, state, path_label, addr, gas):
    global prime_check_list
    global addr_run_time
    global addr_gas_sum

    in_stack = state['Stack']
    in_memory = state['Memory']
    in_storage = state['Storage']
    loop_gas = 0

    new_path = True
    if path_label.count(path_label[-1]) > 1:
        first_idx = path_label.index(path_label[-1])
        curr_path_addr = path_label[:first_idx]

        for index, val in enumerate(node['state']):
            state_path_label = val['Path Label']
            state_path_addr = state_path_label[:first_idx]

            if curr_path_addr == state_path_addr:
                new_path = False
                gas_sum = addr_gas_sum[addr]
                loop_gas = gas - gas_sum
                val['Stack'] = in_stack
                val['Memory'] = in_memory
                val['Storage'] = in_storage
                break
    else:
        addr_gas_sum.update({addr: gas})

        for val in node['state']:
            if val['Path Label'] == path_label:
                new_path = False
                val['Stack'] = in_stack
                val['Memory'] = in_memory
                val['Storage'] = in_storage

    if new_path:
        node['state'].append({'Path Label': path_label, 'Stack': in_stack, 'Memory': in_memory, 'Storage': in_storage})
    return node, loop_gas
