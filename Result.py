import os
from Analyzer import Analyzer
from settings import ROOT_PATH
from Path import Path

class Result:

    def __init__(self, analyzer: Analyzer):
        self.analyzer = analyzer
        self.max_gas = None
        self.constant_path = None
        self.bound_path = None
        self.unbound_path = None

    def set_max_gas(self, gas: int) -> None:
        self.max_gas = gas

    def set_constant_path(self, path: [Path]) -> None:
        self.constant_path = path
    
    def set_bound_path(self, path: [Path]) -> None:
        self.bound_path = path

    def set_unbound_path(self, path: [Path]) -> None:
        self.unbound_path = path

    def render(self, directory: str, file_name: str):
        sep_line = '-|-' * 30
        with open('%s/%s/%s.txt' % (os.path.join(ROOT_PATH, 'result'), directory, file_name), 'w') as f:
            line = '=' * ((90 - len(file_name) - 2)//2)
            f.write('%s %s %s\n' % (line, file_name, line))
            f.write('Total Instruction: %s\n' % self.analyzer.cfg.ins_num())
            f.write('Total nodes: %s\n' % self.analyzer.cfg.node_num())
            f.write('Total edges: %s\n' % self.analyzer.cfg.edge_num())
            # f.write('Total path: %s\n' % len(PATHS))
            if self.constant_path and self.bound_path and self.unbound_path:
                f.write('Constant Gas Path: %s\n' % len(self.constant_path))
                f.write('Bounded Gas Path: %s\n' % len(self.bound_path))
                f.write('Unbounded Gas Path: %s\n' % len(self.unbound_path))
                f.write('Max Gas Consumption: %s\n' % self.max_gas)
                f.write('\n%s\n\n' % sep_line)
                f.write('[SYMBOLIC VARIABLE TABLE]:\n\n')
                for variable in self.analyzer.variables.variables:
                    f.write('[%s]: %s\n' % (variable.name, variable.value))
                f.write('\n%s\n\n' % sep_line)

            # NOTE: Write Constant Path
            if self.constant_path:
                f.write('[CONSTANT PATH]\n\n%s' % self.__add_path_content(self.constant_path))

            if self.bound_path:
                f.write('[BOUNDED PATH]\n\n%s' % self.__add_path_content(self.bound_path))

            if self.unbound_path:
                f.write('[UNBOUNDED PATH]\n\n%s' % self.__add_path_content(self.unbound_path))

    def __add_path_content(self, paths: list) -> str:
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
            content += '\n[Gas]: %s\n%s\n\n' % (gas, sub_sep_line)
        content = content[:-92] + '\n%s\n\n' % sep_line
        return content