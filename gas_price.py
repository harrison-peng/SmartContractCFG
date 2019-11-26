from math import log

gas_constraint_table = {
    'EXP': '10+(1-b)+(10*(1+log256(b))',
    # # 'if(exp=0)?10:10+(10*(1+log256(xy)))',
    # 'SSTORE': '20000*(1-p)*v/v+5000*(1-v)*p/p',
    # # if(p=0 and v!=0)?
    # 'SHA3': '30+6n',
    # 'LOG0': '375+8s',
    # 'LOG1': '2*375+8s',
    # 'LOG2': '3*375+8s',
    # 'LOG3': '4*375+8s',
    # 'LOG4': '5*375+8s',
    # 'CALLDATACOPY': '2+3*s',
    # 'CODECOPY': '2+3*s',
    # 'RETURNDATACOPY': '2+3*s',
    # 'EXTCODECOPY': '700+3*s'
}


def exp(x, y):
    computed = pow(x, y)
    if computed == 0:
        return 10
    else:
        answer = 10 + (10 * (1 + log(computed, 256)))
        return answer


def sstore(p, v):
    if p == 0 and v != 0:
        return 20000
    else:
        return 5000


def sha3(n):
    return 30 + 6 * n


def log_ins(s, ins):
    log_number = ins.split('LOG')[1]
    return (log_number + 1) * 375 + 8 * s


def copy(s):
    return 2 + 3 * s


def extcodecopy(s):
    return 700 + 3 * s


gas_table = {
    'STOP': 0,
    'ADD': 3,
    'MUL': 5,
    'SUB': 3,
    'DIV': 5,
    'SDIV': 5,
    'MOD': 5,
    'SMOD': 5,
    'ADDMOD': 8,
    'MULMOD': 8,
    'SIGNEXTEND': 5,
    'LT': 3,
    'GT': 3,
    'SLT': 3,
    'SGT': 3,
    'EQ': 3,
    'ISZERO': 3,
    'AND': 3,
    'OR': 3,
    'XOR': 3,
    'NOT': 3,
    'BYTE': 3,
    'ADDRESS': 2,
    'PUSHDEPLOYADDRESS': 2,
    'BALANCE': 400,
    'ORIGIN': 2,
    'CALLER': 2,
    'CALLDATALOAD': 3,
    'CALLDATASIZE': 2,
    'RETURNDATASIZE': 2,
    'CODESIZE': 2,
    'GASPRICE': 2,
    'EXTCODESIZE': 700,
    'BLOCKHASH': 20,
    'COINBASE': 2,
    'TIMESTAMP': 2,
    'NUMBER': 2,
    'DIFFICULTY': 2,
    'GASLIMIT': 2,
    'POP': 2,
    'MLOAD': 3,
    'MSTORE': 3,
    'MSTORE8': 3,
    'SLOAD': 200,
    'JUMP': 8,
    'JUMP [in]': 8,
    'JUMP [out]': 8,
    'JUMPI': 10,
    'PC': 2,
    'MSIZE': 2,
    'GAS': 2,
    'JUMPDEST': 1,
    'PUSH': 3,
    'DUP': 3,
    'SWAP': 3,
    'CREATE': 32000,
    # FIXME: CALL, CALLCODE, DELEGATECALL
    'CALL': 700,
    'CALLCODE': 700,
    'RETURN': 0,
    'DELEGATECALL': 700,
    'STATICCALL': 700,
    'INVALID': 0,
    'SELFDESTRUCT': 5000,
    # FIXME: LOG
    'LOG0': 375,
    'LOG1': 750,
    'LOG2': 1125,
    'LOG3': 1500,
    'LOG4': 1875,
    'EXTCODECOPY': 700,
    'CODECOPY': 2,
    'CALLDATACOPY': 2,
    'SHA3': 30,
    'KECCAK': 30,
    'SSTORE': 20000,
    'CALLVALUE': 2,
    'REVERT': 0,
    'tag': 0,
    'EXP': 10,
    'LOG': 375,
    'RETURNDATACOPY': 2,
    'SHL': 3,
    'SHR': 3,
    'SAR': 3
}


# if line.rstrip() != 'RETURN':
            #     stack, storage, memory, jumpdest, gas_f = se.stack_simulation(line, storage, stack, memory,
            #                                                                       jumpdest, 0)

                # if jumpdest != -1:
                #     jumpfound = False
                #     print(jumpdest)
                #     if t == 'tag':
                #         if int(s[1]) == jumpdest:
                #             print(line)
                #             print("FFFFFFFFFFFFFF")
                #             jumpfound = True
                #             jumpdest = -1
