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

                # if addr in [103]:
                #     print('[INS]:', ins)
                #    print('[STACK]:', addr, ins, state['Stack'])
                #     print('[MEM]:', state['Memory'])
                #     print('[STO]:', state['Storage'])
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
                    state, ins_gas, path_constraint, gas_constraint, prev_jumpi_ins, next_true_addr = \
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
                    node, loop_gas = node_add_state(node, new_state, path_addr, addr, gas)

                    # NOTE: Loop Detection
                    if LOOP_DETECTION:
                        if addr not in loop_condition.keys():
                            loop_condition[addr] = None
                        has_loop, cons_val = loop_detection.loop_detection(prev_jumpi_ins, loop_condition[addr])
                    else:
                        if addr not in count_loop.keys():
                            count_loop[addr] = 0
                        if count_loop[addr] == LOOP_ITERATIONS:
                            return
                        else:
                            count_loop[addr] += 1
                            has_loop = False
                            cons_val = None
                    if has_loop:
                        new_var = BitVec(global_vars.get_gen().gen_loop_var(addr), 256)
                        gas_cons.add(state_simulation.add_gas_constraint(new_var, UNSIGNED_BOUND_NUMBER))
                        loop_pc = loop_detection.handle_loop_condition(prev_jumpi_ins, loop_condition, addr,
                                                                       cons_val, new_var)
                        loop_gas_var = simplify(loop_gas * BV2Int(new_var))
                        gas += loop_gas_var
                    else:
                        loop_condition[addr] = prev_jumpi_ins

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
                                    # print('PCPC:', loop_pc, constraint)
                                    path_cons_true.add(constraint)
                                    edges[idx] = edge_change_loop_constraint(edge, constraint)
                            else:
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
                    path_addr_true = copy.deepcopy(path_addr)
                    path_addr_false = copy.deepcopy(path_addr)
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
                elif opcode in ['STOP', 'RETURN', 'REVERT', 'INVALID']:
                    # NOTE: add gas sum to final_gas_sum
                    global_vars.add_final_gas(addr, gas)

                    # NOTE: add addr to path addr
                    path_addr.append(addr)

                    # NOTE: update gas of the node on CFG
                    node = node_add_gas(node, node_gas)

                    # NOTE: Add the state to the node on CFG
                    node_add_state(node, state, path_addr, addr, gas)

                    count_path += 1
                    global_vars.add_total_path_count()

                    for gc in gas_cons.assertions():
                        path_cons.add(gc)
                    # print('[INFO] Checking Satisfiability of Path Constraints on addr %s with %s pc...'
                    #       % (addr, len(path_cons.assertions())))

                    if path_cons.check() == sat:
                        # print(addr)
                        if is_expr(gas) and not isinstance(gas, z3.z3.IntNumRef):
                            if 'loop' in str(gas):
                                unbounded_path += 1
                            else:
                                bounded_path += 1

                            gas_cons = global_vars.get_gas_limit() < gas
                            path_cons.add(gas_cons)
                            if path_cons.check() == sat:
                                print('[INFO] Path Constraints: sat')
                                global_vars.add_sat_path_count()
                                ans = path_cons.model()
                                new_pc_gas = {'path_constraints': path_cons, 'ans': ans, 'gas': gas, 'path': path_addr}
                                global_vars.add_pc_gas(new_pc_gas)
                        else:
                            constant_path += 1
                            if isinstance(gas, z3.z3.IntNumRef):
                                gas = gas.as_long()
                            if gas > global_vars.get_gas_limit() and path_cons.check() == sat:
                                print('[INFO] Path Constraints: sat')
                                global_vars.add_sat_path_count()
                                ans = path_cons.model()
                                new_pc_gas = {'path_constraints': path_cons, 'ans': ans, 'gas': gas, 'path': path_addr}
                                global_vars.add_pc_gas(new_pc_gas)

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
    edge[1]['label'].append(constraint)
    color = edge[1]['color']
    constraint_false = not (isinstance(constraint, bool) and constraint is False)
    edge[1]['color'] = 'brown' if color == 'blue' and constraint_false else edge[1]['color']
    return edge


def edge_change_loop_constraint(edge, constraint):
    edge[1]['label'].pop()
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

    for key in in_stack:
        if not isinstance(in_stack[key], str):
            in_stack[key] = str(in_stack[key])
    for key in in_memory:
        if not isinstance(in_memory[key], str):
            in_memory[key] = str(in_memory[key])
    for key in in_storage:
        if not isinstance(in_storage[key], str):
            in_storage[key] = str(in_storage[key])

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

    if new_path:
        node['state'].append({'Path Label': path_label, 'Stack': in_stack, 'Memory': in_memory, 'Storage': in_storage})
    return node, loop_gas
