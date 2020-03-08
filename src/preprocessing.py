import os
import re
import src.settings as settings
from subprocess import call
from src.settings import logging, ROOT_PATH, SPECILIFY_SOL_VERSION


def source_code_to_opcodes(code_src: str) -> None:
    from src.Result import Result
    code_path = os.path.abspath(os.path.dirname(code_src))
    contract_name = os.path.basename(code_src).split('.')[0]
    set_up_dir(contract_name)

    try:
        opcodes_raw_path = os.path.join(ROOT_PATH, 'opcodes_raw')
        logging.info('Compiling source code to opcodes.')
        
        with open(code_src, 'r') as f:
            source_code = f.read()
        
        version = get_solc_version(source_code)
        if SPECILIFY_SOL_VERSION:
            call(['docker', 'run', '--rm', '-v', '%s:/contracts' % code_path, 'ethereum/solc:%s' % version, '--opcodes', '/contracts/%s.sol' % contract_name, '-o', '/contracts/opcodes_raw', '--overwrite'])
        else:
            call(['solc', '--opcodes', '%s/%s.sol' % (code_path, contract_name), '-o', '%s/opcodes_raw' % code_path, '--overwrite'])
        
        if settings.LINUX_MODE:
            call(['sudo', 'cp', '-r', '%s/opcodes_raw' % code_path, ROOT_PATH])
            call(['sudo', 'rm', '-rf', '%s/opcodes_raw' % code_path])
        else:
            call(['cp', '-r', '%s/opcodes_raw' % code_path, ROOT_PATH])
            call(['rm', '-rf', '%s/opcodes_raw' % code_path])
            
        for file in os.listdir(opcodes_raw_path):
            code_after = ''

            with open('%s/%s' % (opcodes_raw_path, file), 'r') as f:
                code_before = f.read()

            # i = code_before.find('PUSH1 0x80', 1)
            i = code_before.find('STOP PUSH1 0x80')
            if i != -1:
                code_before = code_before[i+5:]

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
    except Exception as e:
        result = Result()
        result.log_error(settings.ADDRESS, 'Compile source code error: %s' % e)
        raise ValueError('Compile source code error: %s' % e)


def bytecode_to_opcodes(file_name: str) -> None:
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

    except Exception as e:
        result = Result()
        result.log_error(settings.ADDRESS, 'Decompile source code error: %s' % e)
        raise ValueError('Decompile source code error: %s' % e)


def set_up_dir(contract_name: str) -> None:
    try:
        logging.info('Setup the opcodes_raw and opcodes directory.')
        opcodes_raw_path = os.path.join(ROOT_PATH, 'opcodes_raw')
        opcodes_path = os.path.join(ROOT_PATH, 'opcodes')
        result_path = settings.OUTPUT_PATH

        if settings.LINUX_MODE:
            call(['sudo', 'rm', '-rf', opcodes_raw_path])
            call(['sudo', 'rm', '-rf', opcodes_path])
            call(['sudo', 'mkdir', opcodes_path])
            call(['sudo', 'mkdir', opcodes_raw_path])
            call(['sudo', 'mkdir', '%s/%s' % (opcodes_path, contract_name)])
            if not os.path.isdir(result_path):
                call(['sudo', 'mkdir', result_path])
            call(['sudo', 'rm', '-rf', os.path.join(result_path, contract_name)])
            call(['sudo', 'mkdir', os.path.join(result_path, contract_name)])
            call(['sudo', 'mkdir', os.path.join(result_path, contract_name, 'cfg')])
        else:
            call(['rm', '-rf', opcodes_raw_path])
            call(['rm', '-rf', opcodes_path])
            call(['mkdir', opcodes_path])
            call(['mkdir', opcodes_raw_path])
            call(['mkdir', '%s/%s' % (opcodes_path, contract_name)])
            if not os.path.isdir(result_path):
                call(['mkdir', result_path])
            call(['rm', '-rf', os.path.join(result_path, contract_name)])
            call(['mkdir', os.path.join(result_path, contract_name)])
            call(['mkdir', os.path.join(result_path, contract_name, 'cfg')])

    except Exception as e:
        result = Result()
        result.log_error(settings.ADDRESS, 'Directory set up error: %s' % e)
        raise ValueError('Directory set up error: %s' % e)

def get_solc_version(code: str) -> str:
    index = code.find('solidity')
    if index == -1:
        return None
    else:
        version_part = code[index:index+200]
        version = re.findall('\d+\.\d+\.\d+', version_part)[0]
        return version
