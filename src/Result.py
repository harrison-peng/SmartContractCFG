import os
import json
import src.settings as settings
from z3 import *
from typing import Any
from src.Analyzer import Analyzer
from src.Path import Path

class Result:

    def __init__(self, analyzer: Analyzer = None, max_gas: int = None, gas_formula: ArithRef = None, constant_path: [Path] = None, bound_path: [Path] = None, unbound_path: [Path] = None):
        self.analyzer = analyzer
        self.max_gas = max_gas
        self.constant_path = constant_path
        self.bound_path = bound_path
        self.unbound_path = unbound_path
        self.gas_formula = gas_formula

    def render(self, directory: str, file_name: str) -> None:
        # NOTE: This file is for Etherscan Analysis
        if len(self.unbound_path) > 0:
            gas_type = 'unbound'
        elif len(self.bound_path):
            gas_type = 'bound'
        else: 
            gas_type = 'constant'
        self.gas_formula = None if self.gas_formula is None else self.to_string(self.gas_formula)
        info = {
            'address': file_name,
            'gas_type': gas_type,
            'ins_num': self.analyzer.cfg.ins_num(),
            'node_num': self.analyzer.cfg.node_num(),
            'edge_num': self.analyzer.cfg.edge_num(),
            'gas_formula': self.gas_formula,
            'max_gas': self.to_string(self.max_gas)
        }
        with open('%s/%s/info.json' % (settings.OUTPUT_PATH, directory), 'w') as f:
            json.dump(info, f)

        sep_line = '-|-' * 30
        with open('%s/%s/%s.txt' % (settings.OUTPUT_PATH, directory, file_name), 'w') as f:
            line = '=' * ((90 - len(file_name) - 2)//2)
            f.write('%s %s %s\n' % (line, file_name, line))
            f.write('Total Instruction: %s\n' % self.analyzer.cfg.ins_num())
            f.write('Total nodes: %s\n' % self.analyzer.cfg.node_num())
            f.write('Total edges: %s\n' % self.analyzer.cfg.edge_num())
            # f.write('Total path: %s\n' % len(PATHS))
            f.write('Constant Gas Path: %s\n' % len(self.constant_path))
            f.write('Bounded Gas Path: %s\n' % len(self.bound_path))
            f.write('Unbounded Gas Path: %s\n' % len(self.unbound_path))
            if self.gas_formula is not None:
                f.write('Max Gas Formula: %s\n' % self.to_string(self.gas_formula))
            f.write('Max Gas Consumption: %s\n' % self.to_string(self.max_gas))
            f.write('\n%s\n\n' % sep_line)
            f.write('[SYMBOLIC VARIABLE TABLE]:\n\n')
            for variable in self.analyzer.variables.variables:
                f.write('[%s]: %s\n' % (variable.name, variable.value))
            f.write('\n%s\n\n' % sep_line)

            # NOTE: Write Constant Path
            if self.constant_path:
                f.write('[CONSTANT PATH]\n\n%s' % self.__add_path_content(self.constant_path, 'constant'))

            if self.bound_path:
                f.write('[BOUNDED PATH]\n\n%s' % self.__add_path_content(self.bound_path, 'bound'))

            if self.unbound_path:
                f.write('[UNBOUNDED PATH]\n\n%s' % self.__add_path_content(self.unbound_path, 'unbound'))

    def log_error(self, directory: str, log: str) -> None:
        if log == 'empty':
            with open('%s/%s/gas_type.txt' % (settings.OUTPUT_PATH, directory), 'w') as f:
                f.write('%s\n' % log)
                f.write('%s\n' % '')
                f.write('%s\n' % '')
                f.write('%s\n' % '')
                f.write('%s\n' % '')
        else:
            with open('%s/%s/error.txt' % (settings.OUTPUT_PATH, directory), 'w') as f:
                f.write(log)

    def __add_path_content(self, paths: list, gas_type: str) -> str:
        sep_line = '-|-' * 30
        sub_sep_line = '-.' * 45
        content = ''
        for path in paths:
            content += '[PATH]: '
            for node in path.path:
                content += '%s ' % node.tag
            content += '\n\n[Path Constraints]:\n'
            for constraint in path.path_constraint:
                content += '%s\n' % str(constraint).replace('\n', '').replace(' ', '')
            content += '\n[Model]:\n'
            for model in path.model:
                content += '[%s]: %s\n' % (model, path.model[model])
            gas = path.model_gas if path.model_gas else path.gas
            if gas_type == 'constant':
                content += '\n[Gas]: %s\n%s\n\n' % (gas, sub_sep_line)
            elif gas_type == 'bound':
                content += '\n[Gas Formula]: %s\n' % path.gas
                content += '[Gas]: %s\n%s\n\n' % (gas, sub_sep_line)
            else:
                content += '\n[Gas]: %s\n%s\n\n' % (gas, sub_sep_line)
        content = content[:-92] + '\n%s\n\n' % sep_line
        return content

    def to_string(self, input: Any) -> str:
        return str(input).replace('\n', '').replace(' ', '').replace(",'", ",\n'")