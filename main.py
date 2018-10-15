import functools
import json
import os
import argparse
import re
import graphviz as gv

from modules import dbconnect as db
from subprocess import check_output, call
from opcode_table import *

f_SE = os.path.join(os.path.dirname(__file__), 'SE')
wSE = open(f_SE, 'w')
loop_graph_count = 0

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("-i", "--i", help="input file name", action='store_true')
    parser.add_argument("-f", "--f", help="read from DB", action='store_true')
    parser.add_argument("-t", "--t", help="testing", action='store_true')
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

            asm_analysis(2, '')
    else:
        print('Must use an argument, -i for individual source code, -f use source code from DB')

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

    f_op = os.path.join(os.path.dirname(__file__), 'opcode')
    f_op_pre = os.path.join(os.path.dirname(__file__), 'opcode_pre')

    try:
        print('\n[INFO] Empty the output directory.')
        call(['rm', '-f', './output/*'])
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

def asm_analysis(mode, contract_id):
    test_mode = 0

    if mode == 2:
        test_mode = 1  # 非測試模式時，分析結果會寫入資料庫

    opcode_data = db.load_assembly_from_db(mode, contract_id)  # 從資料庫中讀取OPCODE

    for d in opcode_data:
        nodes = []
        edges = []
        contract_opcode = d[0]
        contract_name = d[1]
        pre_id = d[2]
        print('contract id = ', contract_id)
        nodes, edges = cfg_construction(contract_opcode, contract_name, pre_id, nodes, edges, 0)  # 將OPCODE建成CFG
        db.update_status_to_db('CFG_CREATED', 'preprocessing', pre_id, test_mode)  # 更新資料庫中分析狀態
        # symbolic_simulation(nodes, edges)
        # cycle_detection(nodes, edges)

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

    g = create_graph(nodes, edges, 'cfg_full_contract')

    db.update_cfg_info_to_db(pre_id, g, 0)

    return nodes, edges

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

def create_graph(n, e, row_id):
    # print('[INFO] Constructing visualizing graph')
    digraph = functools.partial(gv.Digraph, format='svg')
    g = add_edges(add_nodes(digraph(), n), e)
    filename = 'img/{}/g{}'.format(row_id, row_id)
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