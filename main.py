# -*- coding: UTF-8 -*-
import sys
import os
import time
import argparse
import src.preprocessing as preprocessing
import src.settings as settings
from src.settings import logging, ROOT_PATH
from src.Cfg import Cfg
from src.Analyzer import Analyzer
from src.Path import Path
from src.State import State
from src.Result import Result
from src.Variable import Variables


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('-s', '--sourcecode',dest='sourcecode', help='input source code file', action='store_true')
    parser.add_argument('-b', '--bytecode',dest='bytecode', help='input bytecode file', action='store_true')
    parser.add_argument('-code', '--code',dest='code', help='source code')
    parser.add_argument('-r', '--remove-node', dest='removenode', help='remove unreached node from cfg', action='store_true')
    parser.add_argument('-f', '--format', dest='format', help='format of the cfg file. [options: svg, html(default)]', default='html')
    parser.add_argument('-o', '--output', dest='output', help='the output path')
    parser.add_argument('-d', '--debug', dest='debug', help='set logger to DEBUG mode', action='store_true')
    parser.add_argument('-l', '--linux-mode', dest='linuxmode', help='to run on linux, use linux mode', action='store_true')

    args = parser.parse_args()

    if args.debug:
        logging.basicConfig(
            format='%(asctime)s [%(levelname)s]: %(message)s',
            datefmt='%y-%m-%d %H:%M',
            level=logging.DEBUG
        )
    else:
        logging.basicConfig(
            format='%(asctime)s [%(levelname)s]: %(message)s',
            datefmt='%y-%m-%d %H:%M',
            level=logging.INFO
        )

    if args.removenode:
        settings.REMOVE_UNREACHED_NODE = True

    if args.linuxmode:
        settings.LINUX_MODE = True

    if args.format in ['html', 'svg']:
        settings.CFG_FORMAT = args.format
    else:
        logging.error('Wrong cfg format. Accept option are "html" and "svg"')
        exit(0)

    if args.output:
        logging.debug('Output path: %s' % args.output)
        settings.OUTPUT_PATH = args.output

    start_time = time.time()
    if args.sourcecode:
        if args.code == '':
            logging.error('Source code error')
            exit(0)
        else:
            code_src = os.path.abspath(args.code)
            contract_name = os.path.basename(code_src).split('.')[0]

            logging.info('Transforming contract %s source code to opcodes' % contract_name)
            # NOTE: Compile source code to opcodes
            preprocessing.source_code_to_opcodes(code_src)           
    elif args.bytecode:
        if args.code == '':
            logging.error('Byte code error')
            exit(0)
        else:
            f_src = os.path.abspath(args.code)
            contract_name = os.path.basename(f_src).split('.')[0]

            logging.info('Transforming address %s bytecode to opcodes' % contract_name)
            # NOTE: Compile source code to opcodes
            preprocessing.bytecode_to_opcodes(f_src)
    else:
        logging.error('Must use an argument, --help for more details')
    
    # NOTE: Analyze the opcodes
    opcodes_analysis(contract_name)
    end_time = time.time()
    logging.debug('Analysis time: %ss' % (end_time - start_time))
    logging.info('Analysis complete')


def opcodes_analysis(contract_name):
    settings.ADDRESS = contract_name
    opcodes_path = os.path.join(ROOT_PATH, 'opcodes')
    for file in os.listdir('%s/%s' % (opcodes_path, contract_name)):
        settings.DETECT_LOOP = False
        file_name = file.split('.')[0]
        logging.info('Analyze contract %s - %s' % (contract_name, file_name))
        with open('%s/%s/%s' % (opcodes_path, contract_name, file), 'r') as f:
            opcodes = f.read()

        if opcodes != '':
            result_path = os.path.join(ROOT_PATH, 'result') 
            # NOTE: Build CFG
            cfg = Cfg()
            cfg.build_cfg(opcodes)
            settings.CFG_PATH = '%s/%s/cfg/%s' % (settings.OUTPUT_PATH, contract_name, file_name)
            cfg.render('%s/%s/cfg/%s' % (settings.OUTPUT_PATH, contract_name, file_name))
            logging.info('Total instructions: %s' % cfg.ins_num())

            # NOTE: Analysis
            logging.info('Symbolic simulation...')
            analyzer = Analyzer(cfg)
            analyzer.symbolic_execution(0, Path(), State())
            # analyzer.symbolic_execution_from_other_head()
            analyzer.set_paths_id()
            logging.info('CFG node count = %s' % cfg.node_num())
            logging.info('CFG edge count = %s' % cfg.edge_num())
            logging.info('Total path: %s' % len(analyzer.paths))

            if settings.REMOVE_UNREACHED_NODE:
                cfg.remove_unreach_nodes()
                logging.info('CFG reachable node = %s' % cfg.node_num())
            cfg.render('%s/%s/cfg/%s' % (settings.OUTPUT_PATH, contract_name, file_name), analyzer.paths)

            # NOTE: Solve PATHS
            constant_path, bound_path, unbound_path = classify_path(analyzer)
            logging.info('Satisfiability constant gas path: %s' % len(constant_path))
            logging.info('Satisfiability bound gas path: %s' % len(bound_path))
            logging.info('Satisfiability unbound gas path: %s' % len(unbound_path))
            gas_formula = None
            if len(unbound_path) > 0:
                max_gas = unbound_path[-1].gas
            elif len(bound_path) > 0:
                max_gas, gas_formula = solve_path(analyzer.variables, bound_path, get_max_constant_gas(constant_path))
                logging.info('Max gas formula: %s' % gas_formula)
            else:
                max_gas = get_max_constant_gas(constant_path)
            logging.info('Max gas: %s' % max_gas)

            # NOTE: Output Result File
            logging.info('Writting analysis result into file...')
            if gas_formula is None:
                result = Result(
                    analyzer = analyzer,
                    max_gas = max_gas,
                    constant_path = constant_path,
                    bound_path = bound_path,
                    unbound_path = unbound_path
                )
            else:
                result = Result(
                    analyzer = analyzer, 
                    max_gas = max_gas,
                    gas_formula = gas_formula,
                    constant_path = constant_path, 
                    bound_path = bound_path, 
                    unbound_path = unbound_path
                )
            result.render(contract_name, file_name)
            del cfg, analyzer, result
            logging.info('%s finished' % file_name)
        else:
            logging.info('%s is empyty' % file_name)
            result = Result()
            result.log_error(contract_name, 'empty')


def classify_path(analyzer: Analyzer) -> ([Path], [Path], [Path]):
    paths = analyzer.paths
    constant_path = list()
    bound_path = list()
    unbound_path = list()
    for id, path in enumerate(paths):
        logging.debug('Solving the constraints...[%s/%s]' % (id + 1, len(paths)))
        if path.gas_type == 'constant':
            constant_path.append(path)
        elif path.gas_type == 'bound':
            bound_path.append(path)
        elif path.gas_type == 'unbound':
            unbound_path.append(path)
        else:
            logging.error('Gas Type Error')
    return constant_path, bound_path, unbound_path


def solve_path(variables: Variables, bound_path: [Path], gas_limit: int) -> int:
    logging.info('Solving bound paths...')
    max_gas = gas_limit
    gas_formula = gas_limit
    for id, path in enumerate(bound_path):
        logging.debug('Finding max gas...[%s/%s]' % (id + 1, len(bound_path)))
        if path.solve_max_gas(gas_limit):
            path.assign_model(variables)
            if path.model_gas > max_gas:
                max_gas = path.model_gas
                gas_formula = path.gas
    return max_gas, gas_formula


def get_max_constant_gas(paths) -> int:
    if len(paths) > 0:
        return max([path.gas for path in paths])
    else:
        return 0


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
        if len(same_index_list) == 1:
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


if __name__ == '__main__':
    main()
