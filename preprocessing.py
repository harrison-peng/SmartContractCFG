import os
from subprocess import call
from settings import logging


def source_code_to_opcodes(file_name):
    contract_name = os.path.basename(file_name).split('.')[0]
    set_up_dir(contract_name)

    try:
        logging.info('Compiling source code to opcodes.')
        call(['solc', '--opcodes', '-o', './opcodes_raw', '--overwrite', file_name])

        for file in os.listdir("./opcodes_raw"):
            code_after = ''

            with open('./opcodes_raw/%s' % file, 'r') as f:
                code_before = f.read()

            # print(code_before)
            i = code_before.find('PUSH1 0x80', 1)
            code_before = code_before[i:]
            # print(code_before)

            pc = 0
            code_list = code_before.strip().split(' ')
            push = False
            prev_ins = ''
            code_len = len(code_list) - 1

            for index, ele in enumerate(code_list):
                zero_num = 6 - len(str(pc))
                if ele.startswith('PUSH'):
                    byte = int(ele.split('PUSH')[1])
                    code_after += '0' * zero_num + str(pc) + ': ' + ele + ' '
                    push = True
                    pc += byte
                elif ele == '':
                    pass
                elif ele == 'STOP' and prev_ins == 'JUMP':
                    code_after += '0' * zero_num + str(pc) + ': ' + ele
                    break
                elif index == code_len and ele != 'STOP':
                    break
                else:
                    if push:
                        code_after += ele + '\n'
                        push = False
                    else:
                        code_after += '0' * zero_num + str(pc) + ': ' + ele + '\n'
                    pc += 1
                prev_ins = ele

            # NOTE: remove last '\n'
            code_after = code_after[:-1] if code_after.endswith('\n') else code_after

            with open('./opcodes/%s/%s' % (contract_name, file), 'w') as f:
                f.write(code_after)
    except Exception as ex:
        print('Error:', ex)


def bytecode_to_opcodes(file_name):
    contract_name = os.path.basename(file_name).split('.')[0]
    set_up_dir(contract_name)

    try:
        print('\n[INFO] Compiling bytecode to opcodes.')
        call(['evmasm', '-d', '-i', file_name, '-o', './opcodes_raw/%s.opcode' % contract_name])

        code_after = ''
        with open('./opcodes_raw/%s.opcode' % contract_name, 'r') as f:
            for line in f:
                pc = line.split(': ')[0]
                ins = line.split(': ')[1]
                int_pc = int(pc, 16)
                zero_num = 6 - len(str(int_pc))
                code_after += '0' * zero_num + str(int_pc) + ': ' + ins

        # NOTE: remove last '\n'
        code_after = code_after[:-1] if code_after.endswith('\n') else code_after

        with open('./opcodes/%s/%s.opcode' % (contract_name, contract_name), 'w') as f:
            f.write(code_after)

    except Exception as ex:
        print('Error:', ex)


def set_up_dir(contract_name):
    try:
        logging.info('Setup the opcodes_raw and opcodes directory.')
        if not os.path.isdir('./opcodes'):
            call(['mkdir', './opcodes'])
        call(['rm', '-rf', './opcodes_raw'])
        call(['rm', '-rf', './opcodes/%s' % contract_name])
        call(['mkdir', './opcodes_raw'])
        call(['mkdir', './opcodes/%s' % contract_name])
    except Exception as ex:
        print('Error: ', ex)
