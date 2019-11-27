import os
import settings
from subprocess import call
from settings import logging, ROOT_PATH


def copy_file(file):
    try:
        contracts_path = os.path.join(ROOT_PATH, 'contracts')
        call(['rm', '-rf', contracts_path])
        call(['mkdir', contracts_path])
        call(['cp', file, contracts_path])
    except Exception as e:
        raise('Copy file error: %s' % e)


def source_code_to_opcodes(contract_name):
    file_name = os.path.join(ROOT_PATH, 'contracts/%s.sol' % contract_name)
    set_up_dir(contract_name)

    try:
        opcodes_raw_path = os.path.join(ROOT_PATH, 'opcodes_raw')
        logging.info('Compiling source code to opcodes.')
        
        with open(file_name, 'r') as f:
            source_code = f.read()
        
        if '0.4' in source_code[:200]:
            call(['solc', '--opcodes', '-o', opcodes_raw_path, '--overwrite', file_name])
        else:
            call(['docker', 'run', '--rm', '-v', '%s:/SmartContractCFG' % ROOT_PATH, 'ethereum/solc:stable', '--opcodes', 'SmartContractCFG/contracts/%s.sol' % contract_name, '-o', 'SmartContractCFG/opcodes_raw'])

        for file in os.listdir(opcodes_raw_path):
            code_after = ''

            with open('%s/%s' % (opcodes_raw_path, file), 'r') as f:
                code_before = f.read()

            i = code_before.find('PUSH1 0x80', 1)
            code_before = code_before[i:]

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

            with open('%s/%s/%s' % (os.path.join(ROOT_PATH, 'opcodes'), contract_name, file), 'w') as f:
                f.write(code_after)
    except Exception as error:
        logging.error('Compile source code error: %s' % error)
        exit(0)


def bytecode_to_opcodes(file_name):
    contract_name = os.path.basename(file_name).split('.')[0]
    set_up_dir(contract_name)

    try:
        logging.info('Compiling bytecode to opcodes.')
        opcodes_raw_path = os.path.join(ROOT_PATH, 'opcodes_raw')
        call(['evmasm', '-d', '-i', file_name, '-o', '%s/%s.opcode' % (opcodes_raw_path, contract_name)])

        code_after = ''
        with open('%s/%s.opcode' % (opcodes_raw_path, contract_name), 'r') as f:
            for line in f:
                pc = line.split(': ')[0]
                ins = line.split(': ')[1]
                int_pc = int(pc, 16)
                zero_num = 6 - len(str(int_pc))
                code_after += '0' * zero_num + str(int_pc) + ': ' + ins

        # NOTE: remove last '\n'
        code_after = code_after[:-1] if code_after.endswith('\n') else code_after

        with open('%s/%s/%s.opcode' % (os.path.join(ROOT_PATH, 'opcodes'), contract_name, contract_name), 'w') as f:
            f.write(code_after)

    except Exception as error:
        logging.error('Decompile source code error: %s' % error)
        exit(0)


def set_up_dir(contract_name):
    try:
        logging.info('Setup the opcodes_raw and opcodes directory.')
        opcodes_raw_path = os.path.join(ROOT_PATH, 'opcodes_raw')
        opcodes_path = os.path.join(ROOT_PATH, 'opcodes')
        result_path = settings.OUTPUT_PATH
        if not os.path.isdir(opcodes_path):
            call(['mkdir', opcodes_path])
        call(['rm', '-rf', opcodes_raw_path])
        call(['rm', '-rf', '%s/%s' % (opcodes_path, contract_name)])
        call(['mkdir', opcodes_raw_path])
        call(['mkdir', '%s/%s' % (opcodes_path, contract_name)])
        if not os.path.isdir(result_path):
            call(['mkdir', result_path])
        call(['rm', '-rf', os.path.join(result_path, contract_name)])
        call(['mkdir', os.path.join(result_path, contract_name)])
        call(['mkdir', os.path.join(result_path, contract_name, 'cfg')])

    except Exception as error:
        logging.error('Directory set up error: %s' % error)
