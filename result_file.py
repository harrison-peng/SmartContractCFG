import global_vars
from z3_func import *


def output_result(file, contract, nodes_size, edges_size, ins_size, max_gas):
    os.makedirs('./result/%s' % file, exist_ok=True)

    with open('./result/%s/%s.txt' % (file, contract), 'w') as f:
        line = '=' * ((90 - len(contract) - 2)//2)
        f.write('%s %s %s\n' % (line, contract, line))
        f.write('Total Instruction: %s\n' % ins_size)
        f.write('Total nodes: %s\n' % nodes_size)
        f.write('Total edges: %s\n' % edges_size)
        f.write('Total path: %s\n' % global_vars.get_total_path_count())
        f.write('Reachable path: %s\n' % global_vars.get_sat_path_count())
        f.write('Max Gas Consumption: %s\n' % max_gas)
        sep_line = '-|-' * 30
        f.write('%s\n' % sep_line)

        f.write('symbolic variables:\n\n')
        var_table = global_vars.get_var_table()
        for key, val in var_table.items():
            f.write('[%s]: %s,\n\n' % (key, val))
        f.write('%s\n' % sep_line)

        count = 1
        infos = global_vars.get_pc_gas()
        for info in infos:
            f.write('Path No.%s:\n\n' % count)
            f.write('[Path Address]: %s\n\n' % info['path'])
            f.write('[Path Constraints]:\n')
            f.write(str(info['path_constraints']).replace('\n', '').replace(',', ',\n').replace('    ', ' '))

            f.write('\n\n')
            f.write('[Model]:\n')
            f.write(str(info['ans']))
            # pc_var = get_solver_var(info['path_constraints'])
            # for var in pc_var:
            #     if info['ans'][var] is not None:
            #         if isinstance(info['ans'][var], int):
            #             f.write('%s: %s\n' % (var, hex(info['ans'][var])))
            #         else:
            #             f.write('%s: %s\n' % (var, info['ans'][var]))

            f.write('\n\n[Gas]: %s\n\n' % info['gas'])
            f.write('=' * 90)
            f.write('\n\n')

            count += 1

    print('[INFO]: Finished contract <%s> result file\n' % contract)

