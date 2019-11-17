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

            global_vars.set_gas_limit(int(args.gas))

            logging.info('Start Transforming contract %s source code to opcodes.' % contract_name)
            # NOTE: Compile source code to opcodes
            preprocessing.bytecode_to_opcodes(f_src)

            # NOTE: Analyze the opcodes
            opcodes_analysis(contract_name)
    else:
        logging.error('Must use an argument, -s for individual source code')


def opcodes_analysis(contract_name):
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
            logging.info('Total path: %s' % len(PATHS))
            cfg.render('./result/%s/cfg/%s' % (contract_name, file_name))

            # NOTE: Solve PATHS
            logging.info('Solving all the paths...')
            sat_constant_path = list()
            sat_symbolic_path = list()
            for path in PATHS:
                if path.solve():
                    if path.is_constant_gas():
                        sat_constant_path.append(path)
                    else:
                        sat_symbolic_path.append(path)
            logging.info('Satisfiability constant gas path: %s' % len(sat_constant_path))
            logging.info('Satisfiability symbolic gas path: %s' % len(sat_symbolic_path))

            if len(sat_symbolic_path) > 0:
                max_gas = 0
                for path in sat_symbolic_path:
                    path.solve_max_gas(get_max_constant_gas(sat_constant_path))
                    path.assign_model()
                    max_gas = path.model_gas if path.model_gas > max_gas else max_gas
            else:
                max_gas = get_max_constant_gas(sat_constant_path)
                    
            # NOTE: Output Result File
            with open('./result/%s/%s_new.txt' % (contract_name, file_name), 'w') as f:
                line = '=' * ((90 - len(file_name) - 2)//2)
                f.write('%s %s %s\n' % (line, file_name, line))
                f.write('Total Instruction: %s\n' % cfg.ins_num())
                f.write('Total nodes: %s\n' % cfg.node_num())
                f.write('Total edges: %s\n' % cfg.edge_num())
                f.write('Total path: %s\n' % len(PATHS))
                f.write('Constant Gas Path: %s\n' % len(sat_constant_path))
                f.write('Bounded Gas Path: %s\n' % len(sat_symbolic_path))
                f.write('Unbounded Gas Path: %s\n' % len(sat_symbolic_path))
                f.write('Max Gas Consumption: %s\n' % max_gas)
                sep_line = '-|-' * 30
                sub_sep_line = '-.' * 45
                f.write('\n%s\n\n' % sep_line)
                f.write('[SYMBOLIC VARIABLE TABLE]:\n\n')
                for variable in VARIABLES.variables:
                    f.write('[%s]: %s\n' % (variable.name, variable.value))
                f.write('\n%s\n\n' % sep_line)
                f.write('[CONSTANT PATH]\n\n')
                for path in sat_constant_path:
                    f.write('[PATH]: ')
                    for node in path.path:
                        f.write('%s ' % node.tag)
                    f.write('\n\n[Path Constraints]:\n')
                    for constraint in path.path_constraint:
                        f.write('%s\n' % str(constraint).replace('\n', '').replace(' ', ''))
                    f.write('\n[Model]:\n')
                    for model in path.model:
                        f.write('[%s]: %s\n' % (model, path.model[model]))
                    f.write('\n[Gas]: %s\n%s\n\n' % (path.gas, sub_sep_line))

                f.write('\n%s\n\n' % sep_line)
                f.write('[SYMBOLIC PATH]\n\n')
                for path in sat_symbolic_path:
                    f.write('[PATH]: ')
                    for node in path.path:
                        f.write('%s ' % node.tag)
                    f.write('\n\n[Path Constraints]:\n')
                    for constraint in path.path_constraint:
                        f.write('%s\n' % str(constraint).replace('\n', '').replace(' ', ''))
                    f.write('\n[Model]:\n')
                    for model in path.model:
                        f.write('[%s]: %s\n' % (model, path.model[model]))
                    f.write('\n[Gas]: %s\n%s\n\n' % (path.model_gas, sub_sep_line))
                


            # nodes, edges = symbolic_simulation.symbolic_simulation(nodes, edges)
            # graph.create_graph(nodes, edges, contract_name, file_name)
            # max_gas = conformation(nodes)
            # result_file.output_result(contract_name, file_name, nodes_size, edges_size, ins_size, max_gas)

            logging.info('Analysis complete\n')
        else:
            logging.info('%s is empyty\n' % file_name)


def get_max_constant_gas(paths) -> int:
    return max([path.gas for path in paths])


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
