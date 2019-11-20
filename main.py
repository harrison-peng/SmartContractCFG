# -*- coding: UTF-8 -*-
import cfg_builder
import symbolic_simulation
import argparse
import os
import global_vars
import result_file
import graph
import attack_synthesis
import preprocessing
from settings import *
from settings import logging
from Cfg import Cfg
from Analyzer import Analyzer
from Path import Path
from State import State
from Result import Result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('-s', '--sourcecode', help='input source code file', action='store_true')
    parser.add_argument('-b', '--bytecode', help='input bytecode file', action='store_true')
    parser.add_argument('-code', '--code', help='source code')
    parser.add_argument('-gas', '--gas', help='gas limit')

    args = parser.parse_args()

    if args.sourcecode:
        if args.code == '' or args.gas == '':
            logging.error('Source code error')
            exit(0)
        else:
            f_src = os.path.join(os.path.dirname(__file__), args.code)
            contract_name = os.path.basename(f_src).split('.')[0]

            # global_vars.set_gas_limit(int(args.gas))

            logging.info('Start Transforming contract %s source code to opcodes.' % contract_name)
            # NOTE: Compile source code to opcodes
            preprocessing.source_code_to_opcodes(f_src)

            # NOTE: Analyze the opcodes
            opcodes_analysis(contract_name)
    elif args.bytecode:
        if args.code == '' or args.gas == '':
            logging.error('Byte code error')
            exit(0)
        else:
            f_src = os.path.join(os.path.dirname(__file__), args.code)
            contract_name = os.path.basename(f_src).split('.')[0]

            # global_vars.set_gas_limit(int(args.gas))

            logging.info('Start Transforming contract %s source code to opcodes.' % contract_name)
            # NOTE: Compile source code to opcodes
            preprocessing.bytecode_to_opcodes(f_src)

            # NOTE: Analyze the opcodes
            opcodes_analysis(contract_name)
    else:
        logging.error('Must use an argument, -s for individual source code')


def opcodes_analysis(contract_name):
    global PATHS
    for file in os.listdir('./opcodes/%s' % contract_name):
        init_path()
        init_variables()
        file_name = file.split('.')[0]
        logging.info('Analyze contract %s - %s' % (contract_name, file_name))
        with open('./opcodes/%s/%s' % (contract_name, file), 'r') as f:
            opcodes = f.read()

        if opcodes != '':
            global_vars.init()

            # FIXME: old cfg builder
            # nodes, edges, nodes_obj, edges_obj = cfg_builder.cfg_construction(opcodes, file_name)
            # graph.create_graph(nodes, edges, contract_name, file_name)

            # nodes_size, edges_size, ins_size = graph.graph_detail(nodes, edges)
            # print('[INFO] CFG node count = ', nodes_size)
            # print('[INFO] CFG edge count = ', edges_size)
            # print('[INFO] Total instructions: ', ins_size, '\n')

            # nodes, edges = symbolic_simulation.symbolic_simulation(nodes, edges)
            # graph.create_graph(nodes, edges, contract_name, file_name)
            # max_gas = conformation(nodes)
            # result_file.output_result(contract_name, file_name, nodes_size, edges_size, ins_size, max_gas)
            # FIXME: old cfg builder
            
            # NOTE: Build CFG
            cfg = Cfg()
            cfg.build_cfg(opcodes)
            cfg.render('./result/%s/cfg/%s' % (contract_name, file_name))
            logging.info('Total instructions: %s' % cfg.ins_num())

            # NOTE: Analysis
            logging.info('Symbolic simulation...')
            analyzer = Analyzer(cfg)
            analyzer.symbolic_execution(0, Path(), State())
            logging.info('CFG node count = %s' % cfg.node_num())
            logging.info('CFG edge count = %s' % cfg.edge_num())
            logging.info('Total path: %s' % len(analyzer.paths))
            cfg.render('./result/%s/cfg/%s' % (contract_name, file_name))

            # NOTE: Solve PATHS
            max_gas, sat_constant_path, sat_bound_path, sat_unbound_path = solve_path(analyzer.paths)
                    
            # NOTE: Output Result File
            logging.info('Writting analysis result into file...')
            result = Result(cfg, max_gas, sat_constant_path, sat_bound_path, sat_unbound_path)
            result.render(contract_name, file_name)
            del cfg
            logging.info('Analysis complete\n')
        else:
            logging.info('%s is empyty\n' % file_name)


def solve_path(paths: [Path]) -> (int, [Path], [Path], [Path]):
    logging.info('Solving all the paths...')
    sat_constant_path = list()
    sat_bound_path = list()
    sat_unbound_path = list()
    clear_path = remove_duplicate_path(paths)
    for path in clear_path:
        if path.solve():
            gas_type = path.gas_type()
            if gas_type == 'CONSTANT':
                sat_constant_path.append(path)
            elif gas_type == 'BOUND':
                sat_bound_path.append(path)
            else:
                sat_unbound_path.append(path)
    logging.info('Satisfiability constant gas path: %s' % len(sat_constant_path))
    logging.info('Satisfiability bound gas path: %s' % len(sat_bound_path))
    logging.info('Satisfiability unbound gas path: %s' % len(sat_unbound_path))

    if len(sat_unbound_path) > 0:
        max_gas = sat_unbound_path[-1].gas
    elif len(sat_bound_path) > 0:
        logging.info('Finding max gas consumption...')
        max_gas = 0
        for path in sat_bound_path:
            if path.solve_max_gas(get_max_constant_gas(sat_constant_path)):
                path.assign_model()
                max_gas = path.model_gas if path.model_gas > max_gas else max_gas
    else:
        max_gas = get_max_constant_gas(sat_constant_path)

    return max_gas, sat_constant_path, sat_bound_path, sat_unbound_path


def get_max_constant_gas(paths) -> int:
    return max([path.gas for path in paths])


def remove_duplicate_path(paths: [Path]):    
    tags_dict = dict()
    clear_path = list()
    for index, path in enumerate(paths):
        tags = list()
        for node in path.path:
            tags.append(node.tag)
        tags_dict[index] = set(tags)
        # tags_list.append(set(tags))

    while tags_dict:
        find_loop_path = False
        tags = tags_dict[list(tags_dict.keys())[0]]
        same_index_list = [i for i, tag in tags_dict.items() if tag == tags]
        if same_index_list == 1:
            clear_path.append(paths[same_index_list[0]])
        else:
            for index in same_index_list:
                if 'loop' in str(paths[index].gas):
                    clear_path.append(paths[index])
                    find_loop_path = True
                    break
            if not find_loop_path:
                longest_index = (0,0)
                for index in same_index_list:
                    if len(paths[index].path) > longest_index[1]:
                        longest_index = (index, len(paths[index].path))
                clear_path.append(paths[longest_index[0]])
        for index in same_index_list:
            tags_dict.pop(index)
    return clear_path


def conformation(nodes):
    global_vars.init_generator()
    b_paths = global_vars.get_bounded_pc_gas()
    u_paths = global_vars.get_unbounded_pc_gas()
    gas_list = list()
    for path in b_paths:
        model = path['model']
        tags = path['path']
        gas = attack_synthesis.attack_synthesis(tags, nodes, model)
        path['real gas'] = gas
        gas_list.append(gas)

    for path in u_paths:
        model = path['model']
        tags = path['path']
        gas = attack_synthesis.attack_synthesis(tags, nodes, model)
        path['real gas'] = gas
        gas_list.append(gas)

    if gas_list:
        return max(gas_list)
    else:
        return 0


if __name__ == '__main__':
    main()
