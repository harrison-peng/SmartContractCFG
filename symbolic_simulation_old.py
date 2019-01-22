from gas_price import *
import os
import re
import se_ins as se

count_sim = 0
stack = []
storage = []
memory = []
nodes = []
edges = []
count_path = 0
tag_run_time = dict()


f_SE = os.path.join(os.path.dirname(__file__), 'SE')
wSE = open(f_SE, 'w')

def stack_status_constraint(sym_mem, nodes, edges, tag,
                            input_data, f_con, t_con, init_tag,
                            s, gas_sum, con, q,
                            count_condition, conq, gasq):
    global count_sim
    global stack
    global storage
    global memory

    prev_ins = ''
    if count_sim > 10000:
        return gas_sum, nodes, edges, q
    else:
        for n in nodes:
            # print('[node]:', n)
            n_tag = n[0]
            # print('[n_tag]:', n_tag, ', [tag]:', tag)
            if n_tag == tag:
                n_label = n[1].get('label')
                ins_list = n_label.split('\n')

                # NOTE: remove 'TAG' in label
                ins_list = ins_list[2:]

                for ins in ins_list:
                    ins_set = ins.split(': ')
                    line = ins_set[0]
                    opcode = ins_set[1]
                    if line != 'Stack Sum' and line != 'Gas':
                        if len(stack) > 0:
                            wSE.write('{}'.format(str(stack)))
                        wSE.write('\n')
                        wSE.write('{},'.format(str(opcode)))
                    if opcode == 'JUMP':
                        gas_conumption = gas_table[opcode]
                        gas_sum += gas_conumption
                        flag, length, f_con, t_con, stack = se.stack_simulation(opcode, stack, storage, memory, sym_mem,
                                                                                0, 0, input_data, f_con, t_con)
                        # print('[stack sim]:', flag, length, f_con, t_con, stack)

                        # check = prev_ins.split(' ')
                        # if check[1] == '[tag]':
                        #     tag_num = check[2]
                        #     for e in edges:
                        #         if e[0][1] == tag_num and e[0][0] == tag:
                        #             e[1]['color'] = 'red'
                        #     if tag_num < tag:
                        #         init_tag = tag_num
                        #         print('--------------------------------------------------------------------')
                        #         wSE.write(' {0:80} |'.format('X'))
                        #         break
                        #     else:
                        #         wSE.write(' {0:80} |'.format('X'))
                        #         value, init_tag, stack = stack_status_constraint(stack, storage, memory, nodes, edges,
                        #  tag_num, input_data, f_con, t_con, count, init_tag, s)
                        #         if value == 0:
                        #             # print('123')
                        #             break
                        # else:
                        #     continue

                        for e in edges:
                            if e[0][0] == n_tag:
                                # print(e[0][0])
                                for n1 in nodes:
                                    if n1[0] == e[0][1]:
                                        # print(n1[0])
                                        # print(f_con, t_con)
                                        l = n1[1].get('label')
                                        no_pc = False
                                        for l_content in l.split('\n'):
                                            if 'PC' in l_content:
                                                no_pc = False
                                                l_content = l_content.split(': ')
                                                if str(con) != l_content[1]:
                                                    n1[1].update({'label': l + '\n' + 'PC: ' + str(con)})
                                            else:
                                                no_pc = True
                                        if no_pc:
                                            n1[1].update({'label': l + '\n' + 'PC: ' + str(con)})

                                        wSE.write('{},'.format('X'))
                                        count_sim += 1
                                        gas_sum, nodes, edges, q = stack_status_constraint(sym_mem,
                                                                                           nodes, edges, n1[0],
                                                                                           input_data,
                                                                                           f_con, t_con, init_tag, s,
                                                                                           gas_sum, con, q,
                                                                                           count_condition,
                                                                                           conq, gasq)
                    elif opcode == 'JUMPI':
                        gas_conumption = gas_table[opcode]
                        gas_sum += gas_conumption
                        flag, target, f_con, t_con, stack = se.stack_simulation(opcode, stack, storage, memory, sym_mem, 0,
                                                                                0,
                                                                                input_data, f_con, t_con)
                        # print('[stack sim]:', flag, target, f_con, t_con, stack)

                        # check = prev_ins.split(' ')
                        # if flag == 1:
                        #     if check[1] == '[tag]':
                        #         tag_num = check[2]
                        #         for e in edges:
                        #             if e[0][1] == tag_num and e[0][0] == tag:
                        #                 e[1]['color'] = 'red'
                        #         wSE.write(' {0:80} |'.format('X'))
                        #         value, init_tag, stack = stack_status_constraint(stack, storage, memory, nodes, edges, tag_num, input_data, f_con, t_con, count, init_tag, s)
                        #         if value == 0:
                        #             # print('4456')
                        #             break
                        # elif flag == 0:
                        #     tag_num = str(int(check[2]) + 10000)
                        #     for e in edges:
                        #         if e[0][1] == tag_num:
                        #             e[1]['color'] = 'red'
                        #     wSE.write(' {0:80} |'.format('X'))
                        #     value, init_tag, stack = stack_status_constraint(stack, storage, memory, nodes, edges, tag_num, input_data, f_con, t_con, count, init_tag, s)
                        #     if value == 0:
                        #         # print('789')
                        #         break
                        # else:
                        #     constraint_jump(nodes, edges, stack, storage, memory, check, tag, input_data, f_con, t_con, count, init_tag, s)
                        #     break

                        # q = deque([])

                        n[1]['id'] = 'Stack now'
                        # print('[n]:', n[1])
                        for item in stack:
                            n[1]['id'] += ' ' + str(item)
                        start_tag = tag
                        for nn in nodes:
                            if nn[0] == start_tag:
                                tmp = nn[1].get('id').split('Stack now ')
                                if len(tmp) == 1:
                                    stack_new = []
                                else:
                                    stack_new = tmp[1].split(' ')
                                q.append(stack_new)
                                break

                        n[1]['id'] += 'Con now'
                        for item in con:
                            n[1]['id'] += ' ' + str(item)
                        start_tag = tag
                        for nn in nodes:
                            if nn[0] == start_tag:
                                tmp = nn[1].get('id').split('Con now ')
                                if len(tmp) == 1:
                                    con_new = []
                                else:
                                    con_new = tmp[1].split(' ')
                                conq.append(con_new)
                                break

                        n[1]['id'] += 'Gas now ' + str(gas_sum)
                        start_tag = tag
                        for nn in nodes:
                            if nn[0] == start_tag:
                                tmp = nn[1].get('id').split('Gas now ')
                                if len(tmp) == 1:
                                    gas_new = []
                                else:
                                    gas_new = tmp[1]
                                gasq.append(float(gas_new))
                                break

                        count_condition = 0

                        for e in edges:
                            if e[0][0] == n_tag:
                                count_condition += 1
                                if count_condition > 1:
                                    stack = q.pop()
                                    con = conq.pop()
                                    gas_sum = gasq.pop()
                                for n1 in nodes:
                                    if n1[0] == e[0][1]:
                                        # print('To: ', e[0][1])
                                        l = n1[1].get('label')
                                        if int(e[0][1]) > 10000:
                                            if flag != 1 and flag != 0:
                                                no_pc = False
                                                for l_content in l.split('\n'):
                                                    if 'PC' in l_content:
                                                        no_pc = False
                                                        l_content = l_content.split(': ')
                                                        if f_con[-1] != l_content[1]:
                                                            con.append(f_con[-1])
                                                            n1[1].update({'label': l + '\n' + 'PC: ' + str(con)})
                                                    else:
                                                        no_pc = True
                                                if no_pc:
                                                    con.append(f_con[-1])
                                                    n1[1].update({'label': l + '\n' + 'PC: ' + str(con)})
                                                wSE.write('{},'.format(f_con[-1]))
                                            else:
                                                no_pc = False
                                                for l_content in l.split('\n'):
                                                    if 'PC' in l_content:
                                                        no_pc = False
                                                        l_content = l_content.split(': ')
                                                        if str(con) != l_content[1]:
                                                            n1[1].update({'label': l + '\n' + 'PC: ' + str(con)})
                                                    else:
                                                        no_pc = True
                                                if no_pc:
                                                    n1[1].update({'label': l + '\n' + 'PC: ' + str(con)})
                                                wSE.write('{},'.format('X'))
                                        else:
                                            if flag != 1 and flag != 0:
                                                no_pc = False
                                                for l_content in l.split('\n'):
                                                    if 'PC' in l_content:
                                                        no_pc = False
                                                        l_content = l_content.split(': ')
                                                        if t_con[-1] != l_content[1]:
                                                            con.append(t_con[-1])
                                                            n1[1].update({'label': l + '\n' + 'PC: ' + str(con)})
                                                    else:
                                                        no_pc = True
                                                if no_pc:
                                                    con.append(t_con[-1])
                                                    n1[1].update({'label': l + '\n' + 'PC: ' + str(con)})
                                                wSE.write('{},'.format(t_con[-1]))
                                            else:
                                                no_pc = False
                                                for l_content in l.split('\n'):
                                                    if 'PC' in l_content:
                                                        no_pc = False
                                                        l_content = l_content.split(': ')
                                                        if str(con) != l_content[1]:
                                                            n1[1].update({'label': l + '\n' + 'PC: ' + str(con)})
                                                    else:
                                                        no_pc = True
                                                if no_pc:
                                                    n1[1].update({'label': l + '\n' + 'PC: ' + str(con)})
                                                wSE.write('{},'.format('X'))
                                        count_sim += 1
                                        gas_sum, nodes, edges, q = stack_status_constraint(sym_mem,
                                                                                           nodes, edges, n1[0],
                                                                                           input_data,
                                                                                           f_con, t_con, init_tag, s,
                                                                                           gas_sum, con, q,
                                                                                           count_condition,
                                                                                           conq, gasq)
                                        # print('NEXT')

                    # elif i == 'REVERT' or i == 'STOP' or i == 'RETURN' or i == 'JUMP [out]':
                    #     # print('RRRRRRRRRRRRRRRRR')
                    #     return 0, 0, 0

                    elif line == 'Stack Sum' and (prev_ins == 'POP' or prev_ins == 'SWAP1' or 'PUSH' in prev_ins or
                                               prev_ins == 'TIMESTAMP' or prev_ins == 'JUMPDEST'):
                        for e in edges:
                            if e[0][0] == n_tag:
                                for n1 in nodes:
                                    if n1[0] == e[0][1]:
                                        l = n1[1].get('label')
                                        no_pc = False
                                        for l_content in l.split('\n'):
                                            if 'PC' in l_content:
                                                no_pc = False
                                                l_content = l_content.split(': ')
                                                if str(con) != l_content[1]:
                                                    n1[1].update({'label': l + '\n' + 'PC: ' + str(con)})
                                            else:
                                                no_pc = True
                                        if no_pc:
                                            n1[1].update({'label': l + '\n' + 'PC: ' + str(con)})
                                        wSE.write('{},'.format('X'))
                                        count_sim += 1
                                        gas_sum, nodes, edges, q = stack_status_constraint(sym_mem,
                                                                                           nodes, edges, n1[0],
                                                                                           input_data,
                                                                                           f_con, t_con, init_tag, s,
                                                                                           gas_sum, con, q,
                                                                                           count_condition,
                                                                                           conq, gasq)
                    elif line == 'Stack Sum' or line == 'Gas' or line == 'PC':
                        return gas_sum, nodes, edges, q
                    else:
                        flag, target, f_con, t_con, stack = se.stack_simulation(opcode, stack, storage, memory, sym_mem,
                                                                                0, 0, input_data, f_con, t_con)
                        if flag != 'no':
                            gas = flag
                            if isinstance(gas, str):
                                print('Gas Constraint: ', gas)
                            else:
                                gas_sum += gas
                        else:
                            if 'PUSH' in opcode:
                                opcode = opcode.split(' ')[0]
                                gas_conumption = gas_table[opcode]
                                gas_sum += gas_conumption
                            elif 'tag' in opcode:
                                continue
                            else:
                                t = re.sub(r'\d+', '', str(opcode))
                                gas_conumption = gas_table[t]
                                gas_sum += gas_conumption
                        wSE.write('{},'.format('X'))
                    prev_ins = opcode
                    # print('[i]:', i)
                    # wSE.write(' {0:80} |'.format('X'))
                    # if int(init_tag) > 0:
                    #     # print('init_tag = ', init_tag)
                    #     break
        return gas_sum, nodes, edges, q