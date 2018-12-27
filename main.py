# -*- coding: UTF-8 -*-

from gas_price import *
from opcode_table import *
import se_ins as se
import graphviz as gv
import functools
import argparse
import re
import os
from subprocess import check_output, call
import json
import sys

f_SE = os.path.join(os.path.dirname(__file__), 'SE')
wSE = open(f_SE, 'w')
loop_graph_count = 0

# Global Variables
count_sim = 0
stack = []
storage = []
memory = []
nodes = []
edges = []


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("-l", "--l", help="input file without store to db", action='store_true')
    parser.add_argument("-code", "--code", help="source code")

    args = parser.parse_args()

    # -t : 測試模式(測試結果不會寫入資料庫)，需要搭配 -code <filename> 使用

    if args.l:
        if args.code == '':
            print('Error')
            exit(0)
        else:
            f_src = os.path.join(os.path.dirname(__file__), args.code)  # 從使用者輸入讀取檔案
            contract_name = os.path.basename(f_src).split('.')[0]

            print('[INFO] Start Transforming contract {} source code to Assembly.'.format(contract_name))
            preproc(f_src)  # 將SOURCE CODE編譯成OPCODE

            for file in os.listdir("./opcode"):
                file_name, contract_name = file.split('_')
                asm_analysis(file_name, contract_name)

    else:
        print('Must use an argument, -l for individual source code')


def preproc(file_name):
    contract_name = os.path.basename(file_name).split('.')[0]

    try:
        print('\n[INFO] Empty the output directory.')
        call(['rm', '-rf', './output'])
        call(['mkdir', './output'])

        print('\n[INFO] Empty the opcode directory.')
        call(['rm', '-rf', './opcode'])
        call(['rm', '-rf', './opcode_pre'])
        call(['mkdir', './opcode'])
        call(['mkdir', './opcode_pre'])
    except Exception as ex:
        print('Error: ', ex)

    try:
        print('\n[INFO] Compiling source code to assembly.')
        call(['solc', '--asm-json', '-o', './output', '--overwrite', file_name])
    except Exception as ex:
        print('Error: ', ex)

    for file in os.listdir("./output"):
        if file.endswith(".json"):
            f_asm_json = os.path.join("./output", file)
            name = f_asm_json.split('./output/')[1].split('_evm.json')[0]

            try:
                f_op = os.path.join(os.path.dirname(__file__), 'opcode', '%s_%s' % (contract_name, name))
                f_op_pre = os.path.join(os.path.dirname(__file__), 'opcode_pre', '%s_%s' % (contract_name, name))
                w_pre = open(f_op_pre, 'w')
                w_op = open(f_op, 'w')

                with open(f_asm_json, 'r') as fh:
                    opcode_file = json.load(fh)

                    if opcode_file is not None:
                        for key, val in opcode_file.items():
                            if key == '.code':
                                for ins_content in val:
                                    instruction = ''
                                    value = ''
                                    for key1, val1 in ins_content.items():
                                        if key1 == 'value':
                                            value = val1
                                        if key1 == 'name':
                                            instruction = val1
                                    instruction = instruction + ' ' + value + '\n'
                                    w_pre.write(instruction)
                            elif key == '.data':
                                for key1, val1 in val.items():
                                    if key1 == '0':
                                        for key2, val2 in val1.items():
                                            if key2 == '.code':
                                                for ins_content in val2:
                                                    instruction = ''
                                                    value = ''
                                                    for key3, val3 in ins_content.items():
                                                        if key3 == 'value':
                                                            value = val3
                                                        if key3 == 'name':
                                                            instruction = val3
                                                    instruction = instruction + ' ' + value + '\n'
                                                    w_op.write(instruction)

                w_pre.close()
                w_op.close()
            except Exception as ex:
                print('[Error]: ', ex)


def asm_analysis(file_name, contract_name):
    global nodes
    global edges
    nodes = []
    edges = []

    with open('./opcode/%s_%s' % (file_name, contract_name), 'r') as f:
        opcode_data = f.read()

    cfg_construction(opcode_data, contract_name)  # 將OPCODE建成CFG

    print('[INFO] CFG node count = ', len(nodes))
    print('[INFO] CFG edge count = ', len(edges))

    graph_detail()
    create_graph(nodes, edges, 'CFG/%s' % file_name, contract_name)

    # n, e = gas_path(nodes, edges)
    # create_graph(n, e, 'MaxPath/%s' % contract_name, contract_name)

    # print('contract name = ', contract_name)
    # symbolic_simulation(nodes, edges)
    # print('[count sim]:', count_sim)
    # cycle_detection(nodes, edges)


def cfg_construction(opcode_data, contract_name):
    global nodes
    global edges

    print('''[INFO] Constructing CFG for contract '{}'. '''.format(contract_name))

    opcode_list = opcode_data.split('\n')
    for i in range(len(opcode_list)):
        opcode_list[i] = (i, opcode_list[i])

    tag_num = 0
    stack_sum = 0
    tag_line_dict = dict()
    stacks = list()

    for _ in range(10):
        cfg_implement(opcode_list, 0, stacks, tag_num, stack_sum, tag_line_dict)



def cfg_implement(opcode_list, line, stacks, tag_num, stack_sum, tag_line_dict):
    global nodes
    global edges

    segment_ins = ['tag', 'JUMP', 'JUMPI', 'STOP', 'REVERT', 'INVALID', 'RETURN']

    node_content = ''
    prev_ins = ''
    prev_tag = 0
    gas_total = 0
    jump_tag = 0
    from_jumpi = False
    push_tag = list()

    opcode_sublist = opcode_list[line:]
    for index, line in opcode_sublist:
        s = line.rstrip().split(' ')

        if s[0] == '':
            continue
        elif s[0] in segment_ins:
            if s[0] == 'tag':
                tag_line_dict.update({int(s[1]): index})
                if node_content == '':
                    tag_num = int(s[1])
                    node_content += str(index) + ': ' + line.rstrip() + '\n'
                else:
                    node_content += 'Stack Sum: ' + str(stack_sum) + '\n' + 'Gas: ' + str(gas_total)
                    node_exist = is_nodes_exist(tag_num)
                    if not node_exist:
                        node_content = '[TAG: %d]\n\n' % tag_num + node_content
                        nodes.append((str(tag_num), {'label': node_content, 'shape': 'box'}))


                    if from_jumpi:
                        edge_exist = is_edge_exist(prev_tag, tag_num)
                        if not edge_exist:
                            edges.append(((str(prev_tag), str(tag_num)),
                                          {'label': '',
                                           'color': 'blue'}))
                        from_jumpi = False

                    edge_exist = is_edge_exist(tag_num, int(s[1]))
                    if not edge_exist:
                        edges.append(((str(tag_num), s[1]),
                                      {'label': '',
                                       'color': 'blue'}))

                    for push_stack in stacks:
                        if push_stack[-1][1] == tag_num:
                            push_stack.pop()
                            push_stack.append((index, int(s[1])))

                    stack_sum = 0
                    node_content = ''
                    node_content += str(index) + ': ' + line.rstrip() + '\n'
                    prev_tag = tag_num
                    tag_num = int(s[1])
            else:
                # COUNT GAS
                gi = re.sub(r'\d+', '', str(s[0]))
                gas = gas_table[gi]
                gas_total += gas

                if from_jumpi:
                    edge_exist = is_edge_exist(prev_tag, tag_num)
                    if not edge_exist:
                        edges.append(((str(prev_tag), str(tag_num)),
                                      {'label': '',
                                       'color': 'blue'}))
                    from_jumpi = False

                if s[0] == 'JUMP' and len(s) == 1 and len(prev_ins) > 1:
                    push_stack = list()
                    for tag in push_tag:
                        push_stack.append(tag)
                    stacks.append(push_stack)

                    stack_sum -= 1
                    node_content += str(index) + ': ' + line.rstrip() + '\n' + 'Stack Sum: ' + str(
                        stack_sum) + '\n' + 'Gas: ' + str(gas_total)
                    node_exist = is_nodes_exist(tag_num)
                    if not node_exist:
                        node_content = '[TAG: %d]\n\n' % tag_num + node_content
                        nodes.append((str(tag_num), {'label': node_content, 'shape': 'box'}))

                    jump_tag = int(prev_ins[2])
                    edge_exist = is_edge_exist(tag_num, jump_tag)
                    if not edge_exist:
                        edges.append(((str(tag_num), str(jump_tag)),
                                      {'label': '',
                                       'color': 'blue'}))
                    push_tag = list()
                    node_content = ''
                elif s[0] == 'JUMPI':
                    stack_sum -= 2
                    node_content += str(index) + ': ' + line.rstrip() + '\n' + 'Stack Sum: ' + str(
                        stack_sum) + '\n' + 'Gas: ' + str(gas_total)
                    node_exist = is_nodes_exist(tag_num)
                    if not node_exist:
                        node_content = '[TAG: %d]\n\n' % tag_num + node_content
                        nodes.append((str(tag_num), {'label': node_content, 'shape': 'box'}))

                    jump_tag = int(prev_ins[2])
                    edge_exist = is_edge_exist(tag_num, jump_tag)
                    if not edge_exist:
                        edges.append(((str(tag_num), str(jump_tag)),
                                      {'label': '',
                                       'color': 'blue'}))

                    for push_stack in stacks:
                        if tag_num == push_stack[-1][1]:
                            push_stack.pop()
                            for tag in push_tag:
                                push_stack.append(tag)

                    node_content = ''
                    push_tag = list()
                    prev_tag = tag_num
                    from_jumpi = True
                elif len(s) > 1 and s[0] == 'JUMP' and s[1] == '[in]':
                    for push_stack in stacks:
                        if push_stack[-1][1] == tag_num:
                            push_stack.pop()
                            for tag in push_tag:
                                push_stack.append(tag)

                    stack_sum -= 1
                    node_content += str(index) + ': ' + line.rstrip() + '\n' + 'Stack Sum: ' + str(
                        stack_sum) + '\n' + 'Gas: ' + str(gas_total)
                    node_exist = is_nodes_exist(tag_num)
                    if not node_exist:
                        node_content = '[TAG: %d]\n\n' % tag_num + node_content
                        nodes.append((str(tag_num), {'label': node_content, 'shape': 'box'}))
                    edge_exist = is_edge_exist(tag_num, push_tag[-1][1])
                    if not edge_exist:
                        edges.append(((str(tag_num), str(push_tag[-1][1])),
                                      {'label': '',
                                       'color': 'blue'}))

                    node_content = ''
                    push_tag = list()
                    prev_tag = tag_num

                elif len(s) > 1 and s[0] == 'JUMP' and s[1] == '[out]':
                    find_out = False
                    jump_to_line = sys.maxsize
                    jump_to_tag = -1
                    for push_stack in stacks:
                        if len(push_stack) > 1 and push_stack[-1][1] == tag_num:
                            jump_from = push_stack.pop()[1]
                            jump_to = push_stack[-1][1]
                            edge_exist = is_edge_exist(jump_from, jump_to)
                            if not edge_exist:
                                find_out = True
                                if tag_line_dict[push_stack[-1][1]] < jump_to_line:
                                    jump_to_line = tag_line_dict[push_stack[-1][1]]
                                    jump_to_tag = push_stack[-1][1]
                                edges.append(((str(jump_from), str(jump_to)),
                                              {'label': '',
                                               'color': 'blue'}))
                    if find_out:
                        return cfg_implement(opcode_list, jump_to_line,
                                                 stacks, jump_to_tag,
                                                 stack_sum, tag_line_dict)

                    stack_sum -= 1
                    node_content += str(index) + ': ' + line.rstrip() + '\n' + 'Stack Sum: ' + str(
                        stack_sum) + '\n' + 'Gas: ' + str(gas_total)
                    node_exist = is_nodes_exist(tag_num)
                    if not node_exist:
                        node_content = '[TAG: %d]\n\n' % tag_num + node_content
                        nodes.append((str(tag_num), {'label': node_content, 'shape': 'box'}))

                    node_content = ''
                    push_tag = list()
                    prev_tag = tag_num
                else:
                    if s[0] in ['REVERT', 'RETURN']:
                        stack_sum -= 2
                    node_content += str(index) + ': ' + line.rstrip() + '\n' + 'Stack Sum: ' + str(
                        stack_sum) + '\n' + 'Gas: ' + str(gas_total)
                    node_exist = is_nodes_exist(tag_num)
                    if not node_exist:
                        node_content = '[TAG: %d]\n\n' % tag_num + node_content
                        nodes.append((str(tag_num), {'label': node_content, 'shape': 'box'}))
                    node_content = ''
                    push_tag = list()
                tag_num = int(tag_num) + 10000
                stack_sum = 0
                gas_total = 0
        else:
            gi = re.sub(r'\d+', '', str(s[0]))
            gas = gas_table[gi]
            gas_total += gas

            if 'LOG' in s[0]:
                log_number = s[0].split('LOG')[1]
                stack_sum -= int(log_number) + 2
            elif 'PUSH' in s and '[tag]' in s:
                push_tag.append((index, int(s[2])))
                stack_sum += 1
            else:
                instruction = re.sub(r'\d+', '', str(s[0]))
                if instruction == 'PUSHLIB':
                    instruction = 'PUSH'
                tmp = opcode[instruction]
                stack_sum += tmp[1] - tmp[0]

            node_content += str(index) + ': ' + line.rstrip() + '\n'
        prev_ins = s


def is_edge_exist(from_tag, to_tag):
    global edges

    for edge in edges:
        jump_pair = list(map(int, edge[0]))
        if from_tag == jump_pair[0] and to_tag == jump_pair[1]:
            return True
    return False

def is_nodes_exist(tag):
    global nodes

    for node in nodes:
        tag_in_node = int(node[0])
        if tag_in_node == tag:
            return True
    return False


def symbolic_simulation(nodes, edges):
    # stack = []
    # storage = []
    # memory = []
    f_con = []
    t_con = []
    con = []
    q = []
    conq = []
    sym_mem = []
    gasq = []

    # print('[stack begin]:', stack)
    gas_sum, c_nodes, c_edges, q = stack_status_constraint(sym_mem,
                                                           nodes, edges, '0', '',
                                                           f_con, t_con, 0, 0,
                                                           0, con, q, 0,
                                                           conq, gasq)
    # print('[stack final]:', memory)

    print('gas SUM = ', gas_sum)

    # create_graph(c_nodes, c_edges, 'symbolic_simulation')


def stack_status_constraint(sym_mem,
                            nodes, edges, tag, input_data,
                            f_con, t_con, init_tag, s,
                            gas_sum, con, q, count_condition,
                            conq, gasq):
    global count_sim
    global stack
    global storage
    global memory

    prev_ins = ''
    print('[params]:', memory)

    # print(count, tag, gas_sum)
    if count_sim > 50:
        return gas_sum, nodes, edges, q
    else:
        for n in nodes:
            # print('[node]:', n)
            n_tag = n[0]
            # print('[n_tag]:', n_tag, ', [tag]:', tag)
            if n_tag == tag:
                # print('[node]:', n_tag)
                n_label = n[1].get('label')
                ins = n_label.split('\n')
                print('[ins]:', ins)
                for k in ins:
                    p = k.split(': ')
                    i = p[1]
                    j = p[0]
                    # print('[i]:', i, ', [j]:', j)
                    if j != 'Stack Sum' and j != 'Gas':
                        if len(stack) > 0:
                            wSE.write('{}'.format(str(stack)))
                        wSE.write('\n')
                        wSE.write('{},'.format(str(i)))
                    if i == 'JUMP':
                        gas_conumption = gas_table[i]
                        gas_sum += gas_conumption
                        flag, length, f_con, t_con, stack = se.stack_simulation(i, stack, storage, memory, sym_mem, 0,
                                                                                0,
                                                                                input_data, f_con, t_con)
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
                    elif i == 'JUMPI':
                        # print('JUMPIII')
                        gas_conumption = gas_table[i]
                        gas_sum += gas_conumption
                        flag, target, f_con, t_con, stack = se.stack_simulation(i, stack, storage, memory, sym_mem, 0,
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
                                # print('[nn]:', nn)
                                tmp = nn[1].get('id').split('Stack now ')
                                if len(tmp) == 1:
                                    stack_new = []
                                else:
                                    stack_new = tmp[1].split(' ')
                                q.append(stack_new)
                                break

                        n[1]['id'] += 'Con now'
                        # print('[n]:', n[1])
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
                        # print('[n]:', n[1])
                        start_tag = tag
                        for nn in nodes:
                            if nn[0] == start_tag:
                                tmp = nn[1].get('id').split('Gas now ')
                                if len(tmp) == 1:
                                    gas_new = []
                                else:
                                    gas_new = tmp[1]
                                # print(int(56.0))
                                gasq.append(float(gas_new))
                                break

                        count_condition = 0

                        for e in edges:
                            # print('[edge]:', e)
                            if e[0][0] == n_tag:
                                count_condition += 1
                                if count_condition > 1:
                                    stack = q.pop()
                                    con = conq.pop()
                                    gas_sum = gasq.pop()
                                # print('From: ', e[0][0])
                                # print('Stack:', stack)
                                # print('Con: ', con)
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

                    elif j == 'Stack Sum' and (prev_ins == 'POP' or prev_ins == 'SWAP1' or 'PUSH' in prev_ins or
                                               prev_ins == 'TIMESTAMP' or prev_ins == 'JUMPDEST'):
                        for e in edges:
                            if e[0][0] == n_tag:
                                # print(e[0][0])
                                for n1 in nodes:
                                    if n1[0] == e[0][1]:
                                        l = n1[1].get('label')
                                        no_pc = False
                                        for l_content in l.split('\n'):
                                            # print('[content]:', l_content)
                                            if 'PC' in l_content:
                                                no_pc = False
                                                l_content = l_content.split(': ')
                                                if str(con) != l_content[1]:
                                                    n1[1].update({'label': l + '\n' + 'PC: ' + str(con)})
                                            else:
                                                no_pc = True
                                        if no_pc:
                                            n1[1].update({'label': l + '\n' + 'PC: ' + str(con)})
                                        # print(n1[0])
                                        wSE.write('{},'.format('X'))
                                        count_sim += 1
                                        gas_sum, nodes, edges, q = stack_status_constraint(sym_mem,
                                                                                           nodes, edges, n1[0],
                                                                                           input_data,
                                                                                           f_con, t_con, init_tag, s,
                                                                                           gas_sum, con, q,
                                                                                           count_condition,
                                                                                           conq, gasq)
                    elif j == 'Stack Sum' or j == 'Gas' or j == 'PC':
                        # print('GAS = ', gas_sum)
                        # print('Gas constraint:', con)
                        return gas_sum, nodes, edges, q
                    else:
                        flag, target, f_con, t_con, stack = se.stack_simulation(i, stack, storage, memory, sym_mem, 0,
                                                                                0, input_data, f_con, t_con)
                        if flag != 'no':
                            # print(flag)
                            gas = flag
                            # print('gas = ', gas)
                            if isinstance(gas, str):
                                print('Gas Constraint: ', gas)
                            else:
                                gas_sum += gas
                        else:
                            if 'PUSH' in i:
                                i = i.split(' ')[0]
                                gas_conumption = gas_table[i]
                                # print('[opcode]:', i, ', [gas]:', gas_conumption)
                                gas_sum += gas_conumption
                            elif 'tag' in i:
                                continue
                            else:
                                t = re.sub(r'\d+', '', str(i))
                                gas_conumption = gas_table[t]
                                # print('[opcode]:', i, ', [gas]:', gas_conumption)
                                gas_sum += gas_conumption
                        wSE.write('{},'.format('X'))
                    prev_ins = i
                    # print('[i]:', i)
                    # wSE.write(' {0:80} |'.format('X'))
                    # if int(init_tag) > 0:
                    #     # print('init_tag = ', init_tag)
                    #     break

        # create_graph(nodes, edges, 'cfg_with_constraint_{}'.format(666))
        # return 0, init_tag, stack

        return gas_sum, nodes, edges, q


def graph_detail():
    global nodes
    count = 0

    for n in nodes:
        label = n[1].get('label')
        label_content = label.split('\n')
        for l in label_content:
            if 'Stack' in l or 'Gas' in l or 'PC' in l:
                break
            else:
                count += 1

    print('[INFO] Total instructions: ', count)


def create_graph(n, e, dir_name, row_id):
    # print('[INFO] Constructing visualizing graph')
    digraph = functools.partial(gv.Digraph, format='svg')
    g = add_edges(add_nodes(digraph(), n), e)
    filename = 'img/{}/{}'.format(dir_name, row_id)
    g.render(filename=filename)
    # print('[COMPLETE - CFG construction]')

    return g


def add_nodes(graph, nodes):
    for n in nodes:
        if isinstance(n, tuple):
            graph.node(n[0], **n[1])
        else:
            graph.node(n)
    return graph


def add_edges(graph, edges):
    for e in edges:
        if isinstance(e[0], tuple):
            graph.edge(*e[0], **e[1])
        else:
            graph.edge(*e)
    return graph

if __name__ == '__main__':
    main()
