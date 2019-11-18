from Cfg import Cfg
from settings import PATHS, VARIABLES

class Result:

    def __init__(self, cfg: Cfg, max_gas: int, constant_path: list, bounded_path: list, unbounded_path: list):
        self.cfg = cfg
        self.max_gas = max_gas
        self.constant_path = constant_path
        self.bounded_path = bounded_path
        self.unbounded_path = unbounded_path

    def render(self, directory: str, file_name: str):
        sep_line = '-|-' * 30
        with open('./result/%s/%s_new.txt' % (directory, file_name), 'w') as f:
            line = '=' * ((90 - len(file_name) - 2)//2)
            f.write('%s %s %s\n' % (line, file_name, line))
            f.write('Total Instruction: %s\n' % self.cfg.ins_num())
            f.write('Total nodes: %s\n' % self.cfg.node_num())
            f.write('Total edges: %s\n' % self.cfg.edge_num())
            f.write('Total path: %s\n' % len(PATHS))
            f.write('Constant Gas Path: %s\n' % len(self.constant_path))
            f.write('Bounded Gas Path: %s\n' % len(self.bounded_path))
            f.write('Unbounded Gas Path: %s\n' % len(self.unbounded_path))
            f.write('Max Gas Consumption: %s\n' % self.max_gas)
            f.write('\n%s\n\n' % sep_line)
            f.write('[SYMBOLIC VARIABLE TABLE]:\n\n')
            for variable in VARIABLES.variables:
                f.write('[%s]: %s\n' % (variable.name, variable.value))
            f.write('\n%s\n\n' % sep_line)

            # NOTE: Write Constant Path
            if len(self.constant_path) > 0:
                f.write('[CONSTANT PATH]\n\n%s' % self.__add_path_content(self.constant_path))

            if len(self.bounded_path) > 0:
                f.write('[BOUNDED PATH]\n\n%s' % self.__add_path_content(self.bounded_path))

            if len(self.unbounded_path) > 0:
                f.write('[UNBOUNDED PATH]\n\n%s' % self.__add_path_content(self.unbounded_path))

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