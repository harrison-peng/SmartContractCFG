# -*- coding: UTF-8 -*-

from collections import deque
from modules import dbconnect as db
from gas_price import *
from opcode_table import *
import se_ins as se
import sys
import graphviz as gv
import functools
import argparse
import re
import time
import os
import math
from subprocess import check_output, call
import json
from pprint import pprint

f_SE = os.path.join(os.path.dirname(__file__), 'SE')
wSE = open(f_SE, 'w')
loop_graph_count = 0


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("-i", "--i", help="input file name", action='store_true')
    parser.add_argument("-f", "--f", help="read from DB", action='store_true')
    parser.add_argument("-t", "--t", help="testing", action='store_true')
    parser.add_argument("-l", "--l", help="input file without store to db", action='store_true')
    parser.add_argument("-code", "--code", help="source code")

    args = parser.parse_args()

    # 分為三種模式
    # -f : 分析資料庫中還沒跑過的合約
    # -i : 分析單一合約，需要搭配 -code <filename> 使用
    # -t : 測試模式(測試結果不會寫入資料庫)，需要搭配 -code <filename> 使用

    if args.f:
        src = db.load_source_code_from_db()  # 讀取資料庫中全部SOURCE CODE

        for i in src:
            contract_id = i[0]
            code = i[1]
            print('[INFO] Start checking contract {}.\n'.format(contract_id))
            preproc(contract_id, code, 'test.sol', 0)  # 將SOURCE CODE編譯成OPCODE
        asm_analysis(0, '')  # 分析OPCODE(CFG, SYMBOLIC EXECUTION)
    elif args.i:
        if args.code == '':
            print('Error')
            exit(0)
        else:
            f_src = os.path.join(os.path.dirname(__file__), args.code)  # 從使用者輸入讀取檔案

            with open(f_src, 'r') as f:
                src = f.read()  # 讀取檔案內容
                contract = db.update_source_code_to_db(src, 0)  # 將SOURCE CODE存入資料庫
                contract_id = contract[0][0]
                print('[INFO] Start checking contract {}.\n'.format(contract_id))
                preproc(contract_id, src, args.code, 1)  # 將SOURCE CODE編譯成OPCODE

            asm_analysis(1, contract_id)
    elif args.t:
        if args.code == '':
            print('Error')
            exit(0)
        else:
            f_src = os.path.join(os.path.dirname(__file__), args.code)

            with open(f_src, 'r') as f:
                src = f.read()
                print('[INFO] Start checking contract.\n')
                preproc('', src, args.code, 2)

            asm_analysis(2, 1)
    elif args.l:
        if args.code == '':
            print('Error')
            exit(0)
        else:
            f_src = os.path.join(os.path.dirname(__file__), args.code)  # 從使用者輸入讀取檔案
            contract_name = os.path.basename(f_src).split('.')[0]

            with open(f_src, 'r') as f:
                src = f.read()  # 讀取檔案內容
                print('[INFO] Start checking contract {}.\n'.format(contract_name))
                preproc_file(src)  # 將SOURCE CODE編譯成OPCODE

            asm_analysis_file(contract_name)

    else:
        print('Must use an argument, -i for individual source code, -f use source code from DB')


def asm_analysis(mode, contract_id):
    test_mode = 0

    if mode == 2:
        test_mode = 1  # 非測試模式時，分析結果會寫入資料庫

    opcode_data = db.load_assembly_from_db(mode, contract_id)  # 從資料庫中讀取OPCODE
    print(opcode_data)

    for d in opcode_data:
        nodes = []
        edges = []
        contract_opcode = d[0]
        contract_name = d[1]
        pre_id = d[2]
        print('contract id = ', contract_id)
        nodes, edges = cfg_construction(contract_opcode, contract_name, pre_id, nodes, edges, 0)  # 將OPCODE建成CFG
        # db.update_status_to_db('CFG_CREATED', 'preprocessing', pre_id, test_mode)  # 更新資料庫中分析狀態

        n, e = gas_path(nodes, edges)
        create_graph(n, e, 'MaxPath/%s' % contract_name, contract_name)

        # print('contract name = ', contract_name)
        # symbolic_simulation(nodes, edges)
        # cycle_detection(nodes, edges)


def asm_analysis_file(contract_name):
    with open('./opcode/opcode', 'r') as f:
        opcode_data = f.read()

    nodes = []
    edges = []
    contract_opcode = opcode_data
    contract_name = contract_name
    pre_id = 1
    nodes, edges = cfg_construction(contract_opcode, contract_name, pre_id, nodes, edges, 0)  # 將OPCODE建成CFG

    n, e = gas_path(nodes, edges)
    create_graph(n, e, 'MaxPath/%s' % contract_name, contract_name)

    # print('contract name = ', contract_name)
    # symbolic_simulation(nodes, edges)
    # cycle_detection(nodes, edges)


def preproc(contract_id, code, file_name, mode):
    f_src = os.path.join(os.path.dirname(__file__), file_name)

    if mode == 0:
        w_src = open(f_src, 'w')
        w_src.write(code)
        w_src.close()

    if mode == 2:
        test_mode = 1
    else:
        test_mode = 0

    f_op = os.path.join(os.path.dirname(__file__), 'opcode', 'opcode')
    f_op_pre = os.path.join(os.path.dirname(__file__), 'opcode', 'opcode_pre')

    try:
        print('\n[INFO] Empty the output directory.')
        call(['rm', '-rf', './output'])
        call(['mkdir', './output'])
    except Exception as ex:
        print('Error: ', ex)

    try:
        print('\n[INFO] Compiling source code to assembly.')
        call(['solc', '--asm-json', '-o', './output', '--overwrite', f_src])
    except Exception as ex:
        print('Error: ', ex)

    for file in os.listdir("./output"):
        if file.endswith(".json"):
            f_asm_json = os.path.join("./output", file)
            name = f_asm_json.split('./output/')[1].split('_evm.json')[0]

            try:
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

                with open(f_op_pre, 'r') as f:
                    op_pre_content = f.read()
                with open(f_op, 'r') as f1:
                    op_content = f1.read()

                db.update_assembly_to_db(op_content, op_pre_content, contract_id, name, test_mode)
                db.update_status_to_db('DISASSEMBLED', 'contract', contract_id, test_mode)

            except Exception as ex:
                print('[Error]: ', ex)


def preproc_file(file_name):
    f_src = os.path.join(os.path.dirname(__file__), file_name)

    f_op = os.path.join(os.path.dirname(__file__), 'opcode', 'opcode')
    f_op_pre = os.path.join(os.path.dirname(__file__), 'opcode', 'opcode_pre')

    try:
        print('\n[INFO] Empty the output directory.')
        call(['rm', '-rf', './output'])
        call(['mkdir', './output'])
    except Exception as ex:
        print('Error: ', ex)

    try:
        print('\n[INFO] Compiling source code to assembly.')
        call(['solc', '--asm-json', '-o', './output', '--overwrite', f_src])
    except Exception as ex:
        print('Error: ', ex)

    for file in os.listdir("./output"):
        if file.endswith(".json"):
            f_asm_json = os.path.join("./output", file)
            name = f_asm_json.split('./output/')[1].split('_evm.json')[0]

            try:
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

                with open(f_op_pre, 'r') as f:
                    op_pre_content = f.read()
                with open(f_op, 'r') as f1:
                    op_content = f1.read()

            except Exception as ex:
                print('[Error]: ', ex)



def cfg_construction(opcode_data, name, pre_id, nodes, edges, init_tag_num):
    print('''[INFO] Constructing CFG for contract '{}'. '''.format(name))

    opcode_list = opcode_data.split('\n')

    segment_ins = ['tag', 'JUMP', 'JUMPI', 'STOP', 'REVERT', 'INVALID', 'RETURN']

    tag_num = 0 + init_tag_num
    jump_tag = 0
    stack_sum = 0
    gas_total = 0
    prev_tag = 0
    node_content = ''
    prev_ins = ''
    gas_constraint = ''
    tag_value = ''
    jump_out_next_tag = ''
    edge_color = 'blue'
    is_end = []
    push_tag_list = []
    from_jumpi = False
    not_out = False
    from_outer = False
    from_jump_out = False

    # with open(read_file, 'r') as f:
    for idx, line in enumerate(opcode_list):
        s = line.rstrip().split(' ')
        if s[0] == '':
            continue
        elif s[0] in segment_ins:
            if s[0] == 'tag':
                if node_content == '':
                    tag_num = int(s[1]) + init_tag_num
                    node_content += str(idx) + ': ' + line.rstrip() + '\n'
                else:
                    node_content += 'Stack Sum: ' + str(stack_sum) + '\n' + 'Gas: ' + str(
                        gas_total)  # + ' + [' + gas_constraint + ']'
                    nodes.append((str(tag_num), {'label': node_content, 'shape': 'box'}))
                    node_content = ''
                    if from_jumpi:
                        edges.append(((str(prev_tag), str(tag_num)),
                                      {'label': '',
                                       'color': edge_color}))
                        from_jumpi = False
                        # not_out = True
                    node_content += str(idx) + ': ' + line.rstrip() + '\n'
                    prev_tag = tag_num
                    tag_num = int(s[1]) + init_tag_num
                    edges.append(((str(prev_tag), str(tag_num)),
                                  {'label': '',
                                   'color': 'blue'}))
                    stack_sum = 0
            else:
                gi = re.sub(r'\d+', '', str(s[0]))
                gas = gas_table[gi]
                gas_total += gas
                if from_jumpi:
                    edges.append(((str(prev_tag), str(tag_num)),
                                  {'label': '',
                                   'color': edge_color}))
                    from_jumpi = False
                    # not_out = True
                if s[0] == 'JUMP' and len(s) == 1 and len(prev_ins) > 1:
                    stack_sum -= 1
                    node_content += str(idx) + ': ' + line.rstrip() + '\n' + 'Stack Sum: ' + str(
                        stack_sum) + '\n' + 'Gas: ' + str(gas_total)  # + ' + [' + gas_constraint + ']'
                    nodes.append((str(tag_num), {'label': node_content, 'shape': 'box'}))
                    # if from_jump_out:
                    #     jump_tag = int(jump_out_next_tag) + init_tag_num
                    #     from_jump_out = False
                    # else:
                    jump_tag = int(prev_ins[2]) + init_tag_num
                    edges.append(((str(tag_num), str(jump_tag)),
                                  {'label': '',
                                   'color': 'blue'}))
                    node_content = ''
                    not_out = False
                elif s[0] == 'JUMPI':
                    stack_sum -= 2
                    node_content += str(idx) + ': ' + line.rstrip() + '\n' + 'Stack Sum: ' + str(
                        stack_sum) + '\n' + 'Gas: ' + str(gas_total)  # + ' + [' + gas_constraint + ']'
                    nodes.append((str(tag_num), {'label': node_content, 'shape': 'box'}))
                    jump_tag = int(prev_ins[2]) + init_tag_num
                    edges.append(((str(tag_num), str(jump_tag)),
                                  {'label': '',
                                   'color': edge_color}))
                    if from_outer:
                        for i in is_end:
                            edges.append(((str(i), str(tag_num)),
                                          {'label': '',
                                           'color': edge_color}))
                        from_outer = False
                    node_content = ''
                    prev_tag = tag_num
                    from_jumpi = True
                elif len(s) > 1 and s[0] == 'JUMP' and s[1] == '[in]':
                    stack_sum -= 1
                    node_content += str(idx) + ': ' + line.rstrip() + '\n' + 'Stack Sum: ' + str(
                        stack_sum) + '\n' + 'Gas: ' + str(gas_total)  # + ' + [' + gas_constraint + ']'
                    nodes.append((str(tag_num), {'label': node_content, 'shape': 'box'}))
                    jump_tag = int(push_tag_list[-1]) + init_tag_num
                    edges.append(((str(tag_num), str(jump_tag)),
                                  {'label': str(tag_value),
                                   'color': edge_color}))
                    node_content = ''
                    prev_tag = tag_num
                elif len(s) > 1 and s[0] == 'JUMP' and s[1] == '[out]':
                    stack_sum -= 1
                    node_content += str(idx) + ': ' + line.rstrip() + '\n' + 'Stack Sum: ' + str(
                        stack_sum) + '\n' + 'Gas: ' + str(gas_total)  # + ' + [' + gas_constraint + ']'
                    nodes.append((str(tag_num), {'label': node_content, 'shape': 'box'}))
                    # if not not_out:
                    #     edges.append(((str(tag_num), str(int(tag_num) - 1)),
                    #                   {'label': '',
                    #                    'color': edge_color}))
                    not_out = False
                    from_jump_out = True
                    node_content = ''
                    prev_tag = tag_num
                # elif s[0] == 'CREATE' or s[0] == 'CALL':
                #     # # if c2c:
                #     # from_outer = True
                #     # node_content += str(idx) + ': ' + line.rstrip() + '\n' + 'Stack Sum: ' + str(
                #     #     stack_sum) + '\n' + 'Gas: ' + str(gas_total) + ' + [' + gas_constraint + ']'
                #     # nodes.append((str(tag_num), {'label': node_content, 'shape': 'box'}))
                #     # node_content = ''
                #     # if s[0] == 'CREATE':
                #     #     tmp = opcode['CREATE']
                #     #     stack_sum += tmp[1] - tmp[0]
                #     #     f_op_cons = os.path.join(os.path.dirname(__file__), 'opcode_cons')
                #     #     edges.append(((str(tag_num), str(500)),
                #     #                   {'label': '',
                #     #                    'color': edge_color}))
                #     #     nodes, edges, is_end = cfg_construction(f_op_cons, nodes, edges, 500)
                #     # if s[0] == 'CALL':
                #     #     tmp = opcode['CALL']
                #     #     stack_sum += tmp[1] - tmp[0]
                #     #     f_op_two = os.path.join(os.path.dirname(__file__), 'opcode_two')
                #     #     edges.append(((str(tag_num), str(800)),
                #     #                   {'label': '',
                #     #                    'color': edge_color}))
                #     #     nodes, edges, is_end = cfg_construction(f_op_two, nodes, edges, 800)
                #     # else:
                #     instruction = re.sub(r'\d+', '', str(s[0]))
                #     tmp = opcode[instruction]
                #     stack_sum += tmp[1] - tmp[0]
                #     node_content += str(idx) + ': ' + line.rstrip() + '\n'
                #     print(s, tag_num)
                else:
                    if s[0] in ['REVERT', 'RETURN']:
                        stack_sum -= 2
                        if init_tag_num != 0:
                            is_end.append(tag_num)
                    node_content += str(idx) + ': ' + line.rstrip() + '\n' + 'Stack Sum: ' + str(
                        stack_sum) + '\n' + 'Gas: ' + str(gas_total)  # + ' + [' + gas_constraint + ']'
                    nodes.append((str(tag_num), {'label': node_content, 'shape': 'box'}))
                    node_content = ''
                if from_outer:
                    tag_num = int(jump_tag) + 100000 + init_tag_num
                else:
                    tag_num = int(jump_tag) + 10000 + init_tag_num
                stack_sum = 0
                gas_total = 0
                gas_constraint = ''
        else:
            gi = re.sub(r'\d+', '', str(s[0]))
            gas = gas_table[gi]
            gas_total += gas

            if 'LOG' in s[0]:
                log_number = s[0].split('LOG')[1]
                stack_sum -= int(log_number) + 2
            elif 'PUSH' in s and '[tag]' in s:
                push_tag_list.append(s[2])
                stack_sum += 1
            else:
                instruction = re.sub(r'\d+', '', str(s[0]))
                # print(s[0], instruction)
                if instruction == 'PUSHLIB':
                    instruction = 'PUSH'
                tmp = opcode[instruction]
                stack_sum += tmp[1] - tmp[0]

            node_content += str(idx) + ': ' + line.rstrip() + '\n'
        prev_ins = s

    print('[INFO] CFG node count = ', len(nodes))
    print('[INFO] CFG edge count = ', len(edges))

    graph_detail(nodes)

    g = create_graph(nodes, edges, 'CFG/%s' % name, name)

    db.update_cfg_info_to_db(pre_id, g, 0)

    return nodes, edges


def symbolic_simulation(nodes, edges):
    stack = []
    storage = []
    memory = []
    f_con = []
    t_con = []
    con = []
    q = []
    conq = []
    sym_mem = []
    gasq = []
    gas_sum, c_nodes, c_edges, q = stack_status_constraint(stack, storage, memory, sym_mem, nodes, edges, '0', '', f_con, t_con,
                                                           0, 0, 0, 0, con, q, 0, conq, gasq)

    print('gas SUM = ', gas_sum)

    # create_graph(c_nodes, c_edges, 'symbolic_simulation')

def max_gas_path(nodes, edges):
    max_gas = 0

    # indexing nodes
    node_list = list()
    for n in nodes:
        node = {
            'index': n[0],
            'gas': n[1].get('label').split('Gas: ')[1],
            'node': n,
            'check': False
        }
        node_list.append(node)

    tmp_e_list = []
    gas_sum = 0
    run = True
    while(run):
        tmp_n_list = [nodes[0]]
        for n in node_list:
            tmp_gas = 0
            if n in tmp_n_list or len(tmp_n_list) == 0:
                tmp_e = ()
                tmp_n = ()
                for e in edges:
                    is_check = None
                    for node in node_list:
                        if e[0][1] == node['index']:
                            is_check = node['check']

                    if e[0][1] == n[0] and is_check == False:
                        for n1 in nodes:
                            if e[0][1] == n1[0]:
                                gas = n1[1].get('label').split('Gas: ')[1]
                                print('GAS: ' + gas)
                                tmp_gas = int(gas)
                                tmp_e = e
                                tmp_n = n1
                print('tmp_gas:', tmp_gas)
                gas_sum += tmp_gas

                if tmp_e != () and tmp_n != ():
                    tmp_e_list.append(tmp_e)
                    tmp_n_list.append(tmp_n)





def gas_path(nodes, edges):
    # pprint(nodes)
    tmp_n_list = [nodes[0]]
    tmp_e_list = []
    gas_sum = 0
    for n in nodes:
        # print(n[0])
        # tmp_e = ()
        tmp_gas = 0
        # print(tmp_n_list)
        if n in tmp_n_list or len(tmp_n_list) == 0:
            tmp_e = ()
            tmp_n = ()
            for e in edges:
                # pprint(e)
                if e[0][0] == n[0]:
                    # print('Yesssssss')
                    for n1 in nodes:
                        if e[0][1] == n1[0]:
                            gas = n1[1].get('label').split('Gas: ')[1]
                            print('GAS: ' + gas)
                            if tmp_gas == 0:
                                tmp_gas = int(gas)
                                tmp_e = e
                                tmp_n = n1
                            elif int(gas) >= tmp_gas > 0:
                                tmp_gas = int(gas)
                                tmp_e = e
                                tmp_n = n1
            print('tmp_gas:', tmp_gas)
            gas_sum += tmp_gas
            # print(tmp_e, tmp_n)
            if tmp_e != () and tmp_n != ():
                tmp_e_list.append(tmp_e)
                tmp_n_list.append(tmp_n)

    print('GAS SUM: ', gas_sum)
    return tmp_n_list, tmp_e_list


def cycle_detection(nodes, edges):
    visited = []
    rec_stack = []

    start_node = nodes[0]

    dfs_check(start_node, nodes, edges, visited, rec_stack)


def dfs_check(node, nodes, edges, visited, rec_stack):
    stack_impact = 0
    stack_sum = 0
    gas_consumption = 0
    is_jump = False

    visited.append(node)
    rec_stack.append(node)

    node_ins = node[1].get('label').split('\n')

    for i in node_ins:
        i = i.split(': ')[1]
        if i == 'JUMP' or i == 'JUMPI':
            is_jump = True

    for e in edges:
        if e[0][0] == node[0]:
            for n in nodes:
                if n[0] == e[0][1]:
                    neighbour_node = n

                    if neighbour_node not in visited and neighbour_node != '':
                        if dfs_check(neighbour_node, nodes, edges, visited, rec_stack):
                            break
                            # return True
                    elif neighbour_node in rec_stack and is_jump:
                        if int(node[0]) > int(neighbour_node[0]):
                            print('[INFO] Cycle found')

                            start = False

                            for block in rec_stack:
                                block_tag = block[0]
                                if block_tag == neighbour_node[0] or start:
                                    start = True
                                    block_label = block[1].get('label').split('\n')
                                    for block_ins in block_label:
                                        if 'Stack Sum' in block_ins:
                                            stack_impact = int(block_ins.split(': ')[1])
                                            stack_sum += stack_impact

                            # print('Stack : ', stack_sum)

                            loop_graph(rec_stack, edges)

                            if stack_sum > 0:
                                print('[INFO] Positive cycle')
                                print('\n')
                                if stack_sum > 1024:
                                    print('[WARN] STACK OVERFLOW')
                                    return True
                            else:
                                print('[INFO] Not positive cycle')
                                print('\n')
                                return True
                        else:
                            return False

    rec_stack.pop()

    return False


def loop_graph(nodes, edges):

    global loop_graph_count
    loop_graph_count += 1
    create_graph(nodes, edges, './cfg_loop/cfg_loop_part_{}'.format(loop_graph_count))

    # wSE.write('\n\n{},{},{}'.format('Opcode', 'Constraints', 'Stack'))
    # wSE.write('\n')

    stack = []
    storage = []
    memory = []
    f_con = []
    t_con = []
    con = []
    q = []
    conq = []
    sym_mem = []
    gas_sum, c_nodes, c_edges, q = stack_status_constraint(stack, storage, memory, sym_mem, nodes, edges, '0', '',
                                                           f_con, t_con,
                                                           0, 0, 0, 0, con, q, 0, conq)

    print('gas SUM = ', gas_sum)

    create_graph(c_nodes, c_edges, './cfg_constraint/cfg_with_constraints_{}'.format(loop_graph_count))

    print('Done')


def stack_status(src):

    output = []
    f_funchash = os.path.join(os.path.dirname(__file__), 'functionHash')
    f_src = os.path.join(os.path.dirname(__file__), src)

    try:
        w = open(f_funchash, 'w')
        print('\n[INFO] Function Hashes')
        call(['solc', '--combined-json', 'hashes', f_src], stdout=w)
    except Exception as ex:
        print('Error: ', ex)

    with open(f_funchash, 'r') as fh:
        function_dict = json.load(fh)
        for key, val in function_dict.items():
            if key == 'contracts':
                for key2, val2 in val.items():
                    for key3, val3 in val2.items():
                        if key3 == 'hashes':
                            for key4, val4 in val3.items():
                                output.append(val4)

    return output


def stack_simulation_evm(function_input, binrun):

    gas_cost = 0
    input_data = function_input
    f_binary = os.path.join(os.path.dirname(__file__), binrun)
    f_result = os.path.join(os.path.dirname(__file__), 'ana_status')

    try:
        w = open(f_result, 'w')
        try:
            with open(f_binary, 'r') as bf:
                bf_data = bf.readline()
                print('\n[INFO] Stack simulating')
                check_output(['evm', '--debug', '--code', bf_data, '--input', input_data, 'run'], stderr=w)
            w.close()
        except Exception as ex:
            print('[ERROR] Failed to open file \'ana_status.txt\'')
            print('Error: ', ex)
    except Exception as ex:
        print('[ERROR] Failed to open file \'{}\''.format(binrun))
        print('Error: ', ex)


def constraint_jump(nodes, edges, stack, storage, memory, check, tag, input_data, f_con, t_con, count, init_tag, s):
    if count > 8:
        print('count = ', count)
    else:
        count += 1
        for n in nodes:
            n_tag = n[0]
            if n_tag == tag:
                q = deque([])
                n[1]['id'] = '\nStack now'
                print('======================================================== ')
                for item in stack:
                    n[1]['id'] += ' ' + str(item)
                start_tag = tag
                for n1 in nodes:
                    if n1[0] == start_tag:
                        tmp = n1[1].get('id').split('Stack now ')[1]
                        stack_new = tmp.split(' ')
                        q.appendleft(stack_new)
                        break
                # print('q before jumpi = ', q)
                stack_now = q.popleft()
                # print('stack for True = ', stack_now, t_con[-1])
                print('True Constraint: ', t_con[-1])
                wSE.write(' {0:80} |'.format(t_con[-1]))
                tag_num_1 = check[2]
                tag_num_0 = str(int(check[2]) + 10000)
                for e in edges:
                    if e[0][1] == tag_num_1:
                        # e[1]['label'] += '\n' + str(count) + ' ' + str(t_con[-1])
                        e[1]['color'] = 'red'
                        t_con.append(count)
                        t_con.append(tag_num_1)
                        t_con.append(s)
                # print('\n0<<<<<<<<<<0')
                value, init_tag, stack_new_0 = stack_status_constraint(stack_now, storage, memory, nodes, edges,
                                                                       tag_num_1, input_data,
                                                                       f_con, t_con, count, init_tag,
                                                                       str(int(tag_num_1)+int(s)))
                # print(value, init_tag, stack_new_0)
                # print('0>>>>>>>>>>0\n')
                if int(init_tag) > 0 or stack_new_0 == 0:
                    q.appendleft(stack_new_0)
                    # print('XXXXX')
                    for n1 in nodes:
                        if n1[0] == start_tag:
                            tmp = n1[1].get('id').split('Stack now ')[1]
                            stack_new = tmp.split(' ')
                            q.appendleft(stack_new)
                            break
                    stack_now = q.popleft()
                    # print('stack for False = ', stack_now, f_con[-1])
                    print('False Constraint: ', f_con[-1])
                    wSE.write(' {0:80} |'.format(f_con[-1]))
                    for e in edges:
                        if e[0][1] == tag_num_0:
                            # e[1]['label'] += '\n' + str(count) + ' ' + str(f_con[-1])
                            e[1]['color'] = 'red'
                            f_con.append(count)
                            f_con.append(tag_num_0)
                            f_con.append(s)
                    value, init_tag, stack_new_1 = stack_status_constraint(stack_now, storage, memory, nodes, edges,
                                                                           tag_num_0,
                                                                           input_data,
                                                                           f_con, t_con, count, init_tag,
                                                                           str(int(tag_num_0)+int(s)))
                    # print(value, init_tag, stack_new_1)
                    # print('1>>>>>>>>>>1\n')
                    q.append(stack_new_1)

                if int(init_tag) < 1 or count > 4:
                    break
                else:
                    stack_1 = q.popleft()
                    tmp_count = count
                    tag_num_1 = int(tag_num_1) + int(s)
                    # print('tagnum1 = ', tag_num_1)
                    value, init_tag, stack_start = stack_status_constraint(stack_1, storage, memory, nodes, edges,
                                                                           init_tag,
                                                                           input_data,
                                                                           f_con, t_con, count, init_tag,
                                                                           str(tag_num_1))
                    # print(init_tag, stack_start)
                    stack_0 = q.popleft()
                    # print('next stack = ', stack_0)
                    tag_num_0 = int(tag_num_0) + int(s)
                    # print('tagnum0 = ', tag_num_0)
                    value, init_tag, stack_start = stack_status_constraint(stack_0, storage, memory, nodes, edges,
                                                                           init_tag,
                                                                           input_data,
                                                                           f_con, t_con, tmp_count, init_tag,
                                                                           str(tag_num_0))
                    # print(init_tag, stack_start)
                    # print(f_con)
                    # print(t_con)
    # constraint_graph(t_con, f_con)


def stack_status_constraint(stack, storage, memory, sym_mem, nodes, edges, tag, input_data, f_con, t_con, count, init_tag, s,
                            gas_sum, con, q, count_condition, conq, gasq):
    prev_ins = ''
    # print(con)

    # print(count, tag, gas_sum)
    if count > 50:
        return gas_sum, nodes, edges, q
    else:
        for n in nodes:
            n_tag = n[0]
            if n_tag == tag:
                n_label = n[1].get('label')
                ins = n_label.split('\n')
                # print(ins)
                for k in ins:
                    p = k.split(': ')
                    i = p[1]
                    j = p[0]
                    if j != 'Stack Sum' and j != 'Gas':
                        if len(stack) > 0:
                            wSE.write('{}'.format(str(stack)))
                        wSE.write('\n')
                        wSE.write('{},'.format(str(i)))
                    if i == 'JUMP':
                        gas_conumption = gas_table[i]
                        gas_sum += gas_conumption
                        flag, length, f_con, t_con, stack = se.stack_simulation(i, stack, storage, memory, sym_mem, 0, 0,
                                                                                input_data, f_con, t_con)
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
                                        count += 1
                                        gas_sum, nodes, edges, q = stack_status_constraint(stack, storage, memory, sym_mem, nodes,
                                                                                        edges, n1[0], input_data,
                                                                                        f_con, t_con, count, init_tag,
                                                                                        s, gas_sum, con, q,
                                                                                           count_condition, conq, gasq)
                    elif i == 'JUMPI':
                        gas_conumption = gas_table[i]
                        gas_sum += gas_conumption
                        flag, target, f_con, t_con, stack = se.stack_simulation(i, stack, storage, memory, sym_mem, 0, 0,
                                                                                input_data, f_con, t_con)
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
                                # print(int(56.0))
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
                                        count += 1
                                        gas_sum, nodes, edges, q = stack_status_constraint(stack, storage, memory, sym_mem, nodes,
                                                                                        edges, n1[0], input_data,
                                                                                        f_con, t_con, count, init_tag,
                                                                                        s, gas_sum, con, q,
                                                                                           count_condition, conq, gasq)
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
                                        count += 1
                                        gas_sum, nodes, edges, q = stack_status_constraint(stack, storage, memory, sym_mem, nodes,
                                                                                        edges, n1[0], input_data,
                                                                                        f_con, t_con, count, init_tag,
                                                                                        s, gas_sum, con, q,
                                                                                           count_condition, conq, gasq)
                    elif j == 'Stack Sum' or j == 'Gas' or j == 'PC':
                        print('GAS = ', gas_sum)
                        print('Gas constraint:', con)
                        return gas_sum, nodes, edges, q
                    else:
                        flag, target, f_con, t_con, stack = se.stack_simulation(i, stack, storage, memory, sym_mem, 0, 0, input_data, f_con, t_con)
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
                                gas_sum += gas_conumption
                            elif 'tag' in i:
                                continue
                            else:
                                t = re.sub(r'\d+', '', str(i))
                                gas_conumption = gas_table[t]
                                gas_sum += gas_conumption
                        wSE.write('{},'.format('X'))
                    prev_ins = i
                    # wSE.write(' {0:80} |'.format('X'))
                    # if int(init_tag) > 0:
                    #     # print('init_tag = ', init_tag)
                    #     break

        # create_graph(nodes, edges, 'cfg_with_constraint_{}'.format(666))
        # return 0, init_tag, stack

        return gas_sum, nodes, edges, q


def graph_detail(nodes):
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
    digraph = functools.partial(gv.Digraph, format='png')
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


def apply_styles(graph, styles):
    graph.graph_attr.update(
        ('graph' in styles and styles['graph']) or {}
    )
    graph.node_attr.update(
        ('nodes' in styles and styles['nodes']) or {}
    )
    graph.edge_attr.update(
        ('edges' in styles and styles['edges']) or {}
    )
    return graph


if __name__ == '__main__':
    main()
