import os
import global_vars


def output_result(file, contract):
    os.makedirs('./result/%s' % file, exist_ok=True)

    with open('./result/%s/%s.txt' % (file, contract), 'w') as f:
        line = '=' * ((90 - len(contract) - 2)//2)
        f.write('%s %s %s' % (line, contract, line))
        f.write('\n\n')

        count = 1
        infos = global_vars.get_pc_gas()
        for info in infos:
            f.write('Path No.%s:\n\n' % count)
            f.write('[Path Constraints]:\n')
            f.write(str(info['path_constraints']).replace('\n', '').replace(',', ',\n').replace('    ', ' '))

            f.write('\n\n')
            f.write('[Model]:\n%s\n\n' % info['ans'])

            if info['gas'][1] == '':
                f.write('[Gas]: %s\n\n' % info['gas'][0])
            else:
                f.write('[Gas]: %s + (%s)\n\n' % (info['gas'][0], info['gas'][1]))
            f.write('=' * 90)
            f.write('\n\n')

            count += 1

    print('[INFO]: Finished contract <%s> result file' % contract)

