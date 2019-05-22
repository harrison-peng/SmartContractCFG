# -*- coding: UTF-8 -*-
from subprocess import call
import cfg
import symbolic_simulation
import argparse
import os
import json
import global_vars
import result_file
import graph
import attack_synthesis


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("-l", "--l", help="input file without store to db", action='store_true')
    parser.add_argument("-code", "--code", help="source code")
    parser.add_argument('-gas', '--gas', help='gas limit')

    args = parser.parse_args()

    if args.l:
        if args.code == '':
            print('Error')
            exit(0)
        else:
            f_src = os.path.join(os.path.dirname(__file__), args.code)  # 從使用者輸入讀取檔案
            contract_name = os.path.basename(f_src).split('.')[0]

            global_vars.set_gas_limit(int(args.gas))

            print('[INFO] Start Transforming contract {} source code to Assembly.'.format(contract_name))
            # NOTE: 將 SOURCE CODE 編譯成 OPCODE
            preproc(f_src)

            for file in os.listdir("./opcode"):
                file_name, contract_name = file.split('_')
                nodes_size, edges_size, ins_size, nodes = asm_analysis(file_name, contract_name)
                result_file.output_result(file_name, contract_name, nodes_size, edges_size, ins_size)
                conformation(nodes)

    else:
        print('Must use an argument, -l for individual source code')


def preproc(file_name):
    contract_name = os.path.basename(file_name).split('.')[0]

    try:
        print('\n[INFO] Empty the output directory.')
        call(['rm', '-rf', './output'])
        call(['mkdir', './output'])

        print('\n[INFO] Empty the opcode & opcode_pre directory.')
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
    global_vars.init()

    with open('./opcode/%s_%s' % (file_name, contract_name), 'r') as f:
        opcode_data = f.read()

    nodes, edges = cfg.cfg_construction(opcode_data, contract_name)  # 將OPCODE建成CFG

    nodes_size, edges_size, ins_size = graph.graph_detail(nodes, edges)
    print('[INFO] CFG node count = ', nodes_size)
    print('[INFO] CFG edge count = ', edges_size)
    print('[INFO] Total instructions: ', ins_size)
    print('')

    graph.create_graph(nodes, edges, 'CFG/%s' % file_name, contract_name)

    nodes_out, edges_out = symbolic_simulation.symbolic_simulation(nodes, edges)
    nodes_out = graph.node_add_gas_sum(nodes_out)
    try:
        graph.create_graph(nodes_out, edges_out, 'CFG/%s' % file_name, contract_name)
    except Exception as e:
        print('[ERROR] graph drawing error:', e)
    return nodes_size, edges_size, ins_size, nodes_out


def conformation(nodes):
    global_vars.init_generator()
    paths = global_vars.get_pc_gas()
    for path in paths:
        model = path['ans']
        tags = path['tags']
        attack_synthesis.attack_synthesis(tags, nodes, model)


if __name__ == '__main__':
    main()
