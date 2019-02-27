import global_vars


def output_result(file, contract):
    with open('./result/%s/%s.txt' % (file, contract), 'w') as f:
        f.write('====================== %s ======================' % contract)
        f.write('\n\n')

        count = 1
        infos = global_vars.get_pc_gas()
        for info in infos:
            f.write('Path No.%s:\n\n' %count)
            f.write('[Path Constraints]:\n')
            for cons in info['path_constraints']:
                f.write('%s,\n' % str(cons))

            f.write('\n\n')
            f.write('[Answer]: %s\n\n' % info['ans'])
            f.write('[Gas]: %s\n\n' % info['gas'])
            f.write('===========================================')
            f.write('\n\n')

    print('[INFO]: Finished contract %s result file' % contract)

