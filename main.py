# -*- coding: UTF-8 -*-

from subprocess import call
import graphviz as gv
import cfg
import symbolic_simulation
import functools
import argparse
import os
import json
import global_vars
import result_file

f_SE = os.path.join(os.path.dirname(__file__), 'SE')
wSE = open(f_SE, 'w')
loop_graph_count = 0

# Global Variables
count_sim = 0
stack = []
storage = []
memory = []


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("-l", "--l", help="input file without store to db", action='store_true')
    parser.add_argument("-code", "--code", help="source code")

    args = parser.parse_args()

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

    print('[INFO] CFG node count = ', len(nodes))
    print('[INFO] CFG edge count = ', len(edges))

    graph_detail(nodes)
    create_graph(nodes, edges, 'CFG/%s' % file_name, contract_name)

    nodes_out, edges_out = symbolic_simulation.symbolic_simulation(nodes, edges)
    create_graph(nodes_out, edges_out, 'CFG/%s' % file_name, contract_name)
    result_file.output_result(file_name, contract_name)

    result_context = ''
    with open('./result/%s/%s.txt' % (file_name, contract_name), 'r') as f:
        result_context += f.read()
    print('\n%s' % result_context)
    # print('[count sim]:', count_sim)
    # cycle_detection(nodes, edges)


def graph_detail(nodes):
    count = 0

    for n in nodes:
        label = n[1].get('label')
        label_content = label.split('\n')
        for l in label_content:
            if 'Stack' in l or 'Gas' in l or 'PC' in l:
                break
            elif l == '' or (l.startswith('[TAG:') and l.endswith(']')):
                continue
            else:
                count += 1

    print('[INFO] Total instructions: ', count)
    print('')


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
