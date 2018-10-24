import six
from z3 import *
from gas_price import gas_table
import re
import zlib
import base64
import os
import math
from generator import *
import json
import global_params
import sha3


UNSIGNED_BOUND_NUMBER = 2**256 - 1
gen = Generator()
visited_pcs = set()
# storage = []


def main():
    stack = []
    storage = []
    memory = []
    jumpdest = ''
    gas = 0
    # stack_simulation(storage, stack, memory, jumpdest, gas)


def stack_simulation(line, stack, storage, memory, sym_mem, jumpdest, gas, input_data, f_constraint, t_constraint):
    path_conditions_and_vars = {"path_condition": []}
    global_state = get_init_global_state(path_conditions_and_vars)

    # analysis = init_analysis()
    params = Parameter(path_conditions_and_vars=path_conditions_and_vars, global_state=global_state)
    line = line.rstrip()

    if 'tag' in line.split(' ')[0]:
        # print(line)
        condition, target = sym_exec_ins(params, 'JUMPDEST', 0, storage, stack, memory, sym_mem, input_data, f_constraint, t_constraint)
    else:
        # print(line)
        condition, target = sym_exec_ins(params, line, 0, storage, stack, memory, sym_mem, input_data, f_constraint, t_constraint)
    # print('Stack = ', stack)
    return condition, target, f_constraint, t_constraint, stack


class Parameter:
    def __init__(self, **kwargs):
        attr_defaults = {
            "stack": [],
            "calls": [],
            "memory": [],
            "visited": [],
            "mem": {},
            "sha3_list": {},
            "global_state": {},
            "path_conditions_and_vars": {}
        }
        for (attr, default) in six.iteritems(attr_defaults):
            setattr(self, attr, kwargs.get(attr, default))

    # def copy(self):
    #     _kwargs = custom_deepcopy(self.__dict__)
    #     return Parameter(**_kwargs)
    #


def ceil32(x):
    return x if x % 32 == 0 else x + 32 - (x % 32)


def isSymbolic(value):
    # print('is symbolic:')
    # print('six.interger_types = ', six.integer_types)
    # print(isinstance(value, six.integer_types))
    return not isinstance(value, six.integer_types)


def isReal(value):
    return isinstance(value, six.integer_types)


def isAllReal(*args):
    for element in args:
        if isSymbolic(element):
            return False
    return True


def to_symbolic(number):
    if isReal(number):
        return BitVecVal(number, 256)
    return number


def to_unsigned(number):
    if number < 0:
        return number + 2**256
    return number


def to_signed(number):
    if number > 2**(256 - 1):
        return (2**(256) - number) * (-1)
    else:
        return number


def check_sat(solver, pop_if_exception=True):
    try:
        ret = solver.check()
        if ret == unknown:
            raise Z3Exception(solver.reason_unknown())
    except Exception as e:
        if pop_if_exception:
            solver.pop()
        raise e
    return ret


def get_init_global_state(path_conditions_and_vars):
    global_state = {"balance": {}, "pc": 0}
    init_is = init_ia = deposited_value = sender_address = receiver_address = gas_price = origin = currentCoinbase = currentNumber = currentDifficulty = currentGasLimit = callData = None

    if global_params.INPUT_STATE:
        with open('state.json') as f:
            state = json.loads(f.read())
            if state["Is"]["balance"]:
                init_is = int(state["Is"]["balance"], 16)
            if state["Ia"]["balance"]:
                init_ia = int(state["Ia"]["balance"], 16)
            if state["exec"]["value"]:
                deposited_value = 0
            if state["Is"]["address"]:
                sender_address = int(state["Is"]["address"], 16)
            if state["Ia"]["address"]:
                receiver_address = int(state["Ia"]["address"], 16)
            if state["exec"]["gasPrice"]:
                gas_price = int(state["exec"]["gasPrice"], 16)
            if state["exec"]["origin"]:
                origin = int(state["exec"]["origin"], 16)
            if state["env"]["currentCoinbase"]:
                currentCoinbase = int(state["env"]["currentCoinbase"], 16)
            if state["env"]["currentNumber"]:
                currentNumber = int(state["env"]["currentNumber"], 16)
            if state["env"]["currentDifficulty"]:
                currentDifficulty = int(state["env"]["currentDifficulty"], 16)
            if state["env"]["currentGasLimit"]:
                currentGasLimit = int(state["env"]["currentGasLimit"], 16)
    else:
        sender_address = BitVec("Is", 256)
        receiver_address = BitVec("Ia", 256)
        deposited_value = BitVec("Iv", 256)
        init_is = BitVec("init_Is", 256)
        init_ia = BitVec("init_Ia", 256)

    path_conditions_and_vars["Is"] = sender_address
    path_conditions_and_vars["Ia"] = receiver_address
    path_conditions_and_vars["Iv"] = deposited_value

    constraint = deposited_value # (deposited_value >= BitVecVal(0, 256))
    path_conditions_and_vars["path_condition"].append(constraint)
    constraint = (init_is >= deposited_value)
    path_conditions_and_vars["path_condition"].append(constraint)
    constraint = (init_ia >= BitVecVal(0, 256))
    path_conditions_and_vars["path_condition"].append(constraint)

    # update the balances of the "caller" and "callee"

    global_state["balance"]["Is"] = (init_is - deposited_value)
    global_state["balance"]["Ia"] = (init_ia + deposited_value)

    if not gas_price:
        new_var_name = gen.gen_gas_price_var()
        gas_price = new_var_name # BitVec(new_var_name, 256)
        path_conditions_and_vars[new_var_name] = gas_price

    if not origin:
        new_var_name = gen.gen_origin_var()
        origin = new_var_name # BitVec(new_var_name, 256)
        path_conditions_and_vars[new_var_name] = origin

    if not currentCoinbase:
        new_var_name = "IH_c"
        currentCoinbase = new_var_name # BitVec(new_var_name, 256)
        path_conditions_and_vars[new_var_name] = currentCoinbase

    if not currentNumber:
        new_var_name = "IH_i"
        currentNumber = new_var_name # BitVec(new_var_name, 256)
        path_conditions_and_vars[new_var_name] = currentNumber

    if not currentDifficulty:
        new_var_name = "IH_d"
        currentDifficulty = new_var_name # BitVec(new_var_name, 256)
        path_conditions_and_vars[new_var_name] = currentDifficulty

    if not currentGasLimit:
        new_var_name = "IH_l"
        currentGasLimit = new_var_name # BitVec(new_var_name, 256)
        path_conditions_and_vars[new_var_name] = currentGasLimit

    new_var_name = "IH_s"
    currentTimestamp = new_var_name # BitVec(new_var_name, 256)
    path_conditions_and_vars[new_var_name] = currentTimestamp

    # the state of the current current contract
    if "Ia" not in global_state:
        global_state["Ia"] = {}
    global_state["miu_i"] = 0
    global_state["value"] = deposited_value
    global_state["sender_address"] = sender_address
    global_state["receiver_address"] = receiver_address
    global_state["gas_price"] = gas_price
    global_state["origin"] = origin
    global_state["currentCoinbase"] = currentCoinbase
    global_state["currentTimestamp"] = currentTimestamp
    global_state["currentNumber"] = currentNumber
    global_state["currentDifficulty"] = currentDifficulty
    global_state["currentGasLimit"] = currentGasLimit

    return global_state


# Symbolically executing an instruction
def sym_exec_ins(params, instr, block, storage, stack, memory, sym_mem, input_data,  f_constraint, t_constraint):
    global MSIZE
    global visited_pcs
    global solver
    global vertices
    global edges
    global g_src_map
    global calls_affect_state
    global data_source

    # stack = params.stack
    mem = params.mem
    # memory = params.memory
    global_state = params.global_state
    sha3_list = params.sha3_list
    path_conditions_and_vars = params.path_conditions_and_vars
    # analysis = params.analysis
    calls = params.calls

    # print("stack = ", stack)
    # print("memory = ", memory)
    # print("storage = ", storage)
    # print("\n")
    visited_pcs.add(global_state["pc"])

    instr_parts = str.split(instr, ' ')
    opcode = instr_parts[0]

    if opcode == "INVALID":
        print('inininivalid')
        global_state["pc"] += 1
    # elif opcode == "ASSERTFAIL":
    #     if g_src_map:
    #         source_code = g_src_map.get_source_code(global_state['pc'])
    #         source_code = source_code.split("(")[0]
    #         func_name = source_code.strip()
    #         if check_sat(solver, False) != unsat:
    #             model = solver.model()
    #         if func_name == "assert":
    #             global_problematic_pcs["assertion_failure"].append(Assertion(global_state["pc"], model))
    #         elif func_call != -1:
    #             global_problematic_pcs["assertion_failure"].append(Assertion(func_call, model))
    #     return

    # collecting the analysis result by calling this skeletal function
    # this should be done before symbolically executing the instruction,
    # since SE will modify the stack and mem
    # update_analysis(analysis, opcode, stack, mem, global_state, path_conditions_and_vars, solver)
    # if opcode == "CALL" and analysis["reentrancy_bug"] and analysis["reentrancy_bug"][-1]:
    #     global_problematic_pcs["reentrancy_bug"].append(global_state["pc"])

    # log.debug("==============================")
    # log.debug("EXECUTING: " + instr)

    #
    #  0s: Stop and Arithmetic Operations
    #
    elif opcode == "STOP":
        global_state["pc"] += 1
    elif opcode == "TIMESTAMP":
        stack.insert(0, 'TIMESTAMP')
        global_state["pc"] += 1
    elif opcode == "REVERT":
        global_state["pc"] += 1
    elif opcode == "ADD":
        if len(stack) > 1:
            global_state["pc"] += + 1
            first = stack.pop(0)
            second = stack.pop(0)

            # Type conversion is needed when they are mismatched
            # if isReal(first) and isSymbolic(second):
            #     first = BitVecVal(first, 256)
            #     computed = first + second
            # elif isSymbolic(first) and isReal(second):
            #     second = BitVecVal(second, 256)
            # print('first = ' + str(first) + ' type= ' + str(type(first)))
            # print('second = ' + str(second) + ' type= ' + str(type(second)))

            if isinstance(first, int) and isinstance(second, int):
                computed = first + second
            else:
                try:
                    first = int(first)
                except ValueError:
                    first = first
                try:
                    second = int(second)
                except ValueError:
                    second = second

                if isinstance(first, str):
                    computed = '(' + first + '+' + str(second) + ')'
                elif isinstance(second, str):
                    computed = '(' + str(first) + '+' + second + ')'
                elif isinstance(first, str) and isinstance(second, str):
                    # computed = '0x{:x}'.format(int(first + second))
                    computed = '(' + str(first) + '+' + str(second) + ')'
                else:
                    computed = first + second

            # else:
            #     # both are real and we need to manually modulus with 2 ** 256
            #     # if both are symbolic z3 takes care of modulus automatically
            #     computed = (first + second) % (2 ** 256)
            # computed = simplify(computed) if is_expr(computed) else computed
            # check_revert = False
            # if jump_type[block] == 'conditional':
            #     jump_target = vertices[block].get_jump_target()
            #     falls_to = vertices[block].get_falls_to()
            #     check_revert = any([True for instruction in vertices[jump_target].get_instructions() if instruction.startswith('REVERT')])
            #     if not check_revert:
            #         check_revert = any([True for instruction in vertices[falls_to].get_instructions() if instruction.startswith('REVERT')])
            #
            # if jump_type[block] != 'conditional' or not check_revert:
            #     if not isAllReal(computed, first):
            #         solver.push()
            #         solver.add(UGT(first, computed))
            #         if check_sat(solver) == sat:
            #             global_problematic_pcs['integer_overflow'].append(Overflow(global_state['pc'] - 1, solver.model()))
            #         solver.pop()

            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "MUL":
        if len(stack) > 1:
            # global_state["pc"] += 1

            first = stack.pop(0)
            second = stack.pop(0)

            # if isReal(first) and isSymbolic(second):
            #     first = BitVecVal(first, 256)
            # elif isSymbolic(first) and isReal(second):
            #     second = BitVecVal(second, 256)

            if isinstance(first, int) and isinstance(second, int):
                computed = first * second & UNSIGNED_BOUND_NUMBER
            else:
                # try:
                #     first = int(first, 16)
                # except:
                #     first = first
                # try:
                #     second = int(second, 16)
                # except:
                #     second = second
                if isinstance(first, str):
                    computed = '(' + first + '*' + str(second) + ')'
                elif isinstance(second, str):
                    computed = '(' + str(first) + '*' + second + ')'
                else:
                    # computed = '0x{:x}'.format(int(first * second))
                    computed = '(' + str(first) + '*' + str(second) + ')'
            # computed = simplify(computed) if is_expr(computed) else computed
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "SUB":
        if len(stack) > 1:
            # global_state["pc"] += 1
            first = stack.pop(0)
            second = stack.pop(0)
            # if isReal(first) and isSymbolic(second):
            #     first = BitVecVal(first, 256)
            #     computed = first - second
            # elif isSymbolic(first) and isReal(second):
            #     second = BitVecVal(second, 256)
            #     computed = first - second
            # else:
            if isinstance(first, int) and isinstance(second, int):
                computed = (first - second) #% (2 ** 256)
            else:
                try:
                    first = int(first)
                except ValueError as ex:
                    print(ex)
                    first = first
                try:
                    second = int(second)
                except ValueError as ex:
                    print(ex)
                    second = second

                if isinstance(first, str):
                    computed = '(' + first + '-' + str(second) + ')'
                elif isinstance(second, str):
                    computed = '(' + str(first) + '-' + second + ')'
                elif isinstance(first, str) and isinstance(second, str):
                    # computed = '0x{:x}'.format(int(first + second))
                    computed = '(' + str(first) + '-' + str(second) + ')'
                else:
                    computed = first - second
                # try:
                #     first = int(first, 16)
                # except:
                #     first = first
                # try:
                #     second = int(second, 16)
                # except:
                #     second = second
                # if isinstance(first, str):
                #     computed = '(' + first + '-' + str(second) + ')'
                # elif isinstance(second, str):
                #     computed = '(' + str(first) + '-' + second + ')'
                # else:
                #     # computed = '0x{:x}'.format(int(first - second))
                #     computed = '(' + str(first) + '-' + str(second) + ')'
            # computed = simplify(computed) if is_expr(computed) else computed

            # check_revert = False
            # if jump_type[block] == 'conditional':
            #     jump_target = vertices[block].get_jump_target()
            #     falls_to = vertices[block].get_falls_to()
            #     check_revert = any([True for instruction in vertices[jump_target].get_instructions() if instruction.startswith('REVERT')])
            #     if not check_revert:
            #         check_revert = any([True for instruction in vertices[falls_to].get_instructions() if instruction.startswith('REVERT')])
            #
            # if jump_type[block] != 'conditional' or not check_revert:
            #     if not isAllReal(first, second):
            #         solver.push()
            #         solver.add(UGT(second, first))
            #         if check_sat(solver) == sat:
            #             global_problematic_pcs['integer_underflow'].append(Underflow(global_state['pc'] - 1, solver.model()))
            #         solver.pop()

            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "DIV":
        computed = 0
        if len(stack) > 1:
            global_state["pc"] += 1
            first = stack.pop(0)
            second = stack.pop(0)
            if isinstance(first, int) and isinstance(second, int):
                if second == 0:
                    computed = 0
                else:
                    first = to_unsigned(first)
                    second = to_unsigned(second)
                    computed = int(first / second)
            else:
                # if isinstance(first, str):
                #     first = int(first, 16)
                # if isinstance(second, str):
                #     second = int(second, 16)
                # computed = '0x{:x}'.format(int(first / second))

                # try:
                #     first = int(first, 16)
                # except:
                #     first = first
                # try:
                #     second = int(second, 16)
                # except:
                #     second = second
                if isinstance(first, str):
                    computed = '(' + first + '/' + str(second) + ')'
                elif isinstance(second, str):
                    computed = '(' + str(first) + '/' + second + ')'
                else:
                    # computed = '0x{:x}'.format(int(first / second))
                    computed = '(' + str(first) + '/' + str(second) + ')'
            # else:
            #     first = to_symbolic(first)
            #     second = to_symbolic(second)
            #     solver.push()
            #     solver.add( Not (second == 0) )
            #     if check_sat(solver) == unsat:
            #         computed = 0
            #     else:
            #         computed = UDiv(first, second)
            #     solver.pop()
            # computed = simplify(computed) if is_expr(computed) else computed
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "SDIV":
        if len(stack) > 1:
            global_state["pc"] += 1
            first = stack.pop(0)
            second = stack.pop(0)
            if isAllReal(first, second):
                first = to_signed(first)
                second = to_signed(second)
                if second == 0:
                    computed = 0
                elif first == -2**255 and second == -1:
                    computed = -2**255
                else:
                    sign = -1 if (first / second) < 0 else 1
                    computed = sign * ( abs(first) / abs(second) )
            else:
                first = to_symbolic(first)
                second = to_symbolic(second)
                solver.push()
                solver.add(Not(second == 0))
                if check_sat(solver) == unsat:
                    computed = 0
                else:
                    solver.push()
                    solver.add( Not( And(first == -2**255, second == -1 ) ))
                    if check_sat(solver) == unsat:
                        computed = -2**255
                    else:
                        solver.push()
                        solver.add(first / second < 0)
                        sign = -1 if check_sat(solver) == sat else 1
                        z3_abs = lambda x: If(x >= 0, x, -x)
                        first = z3_abs(first)
                        second = z3_abs(second)
                        computed = sign * (first / second)
                        solver.pop()
                    solver.pop()
                solver.pop()
            computed = simplify(computed) if is_expr(computed) else computed
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "MOD":
        if len(stack) > 1:
            global_state["pc"] += 1
            first = stack.pop(0)
            second = stack.pop(0)

            if isinstance(first, int) and isinstance(second, int):
                if second == 0:
                    computed = 0
                else:
                    first = to_unsigned(first)
                    second = to_unsigned(second)
                    computed = first % second & UNSIGNED_BOUND_NUMBER
            else:
                # if isinstance(first, str):
                #     first = int(first, 16)
                # if isinstance(second, str):
                #     second = int(second, 16)
                # computed = '0x{:x}'.format(int(first / second))

                # try:
                #     first = int(first, 16)
                # except:
                #     first = first
                # try:
                #     second = int(second, 16)
                # except:
                #     second = second
                if isinstance(first, str):
                    computed = '(' + first + '%' + str(second) + ')'
                elif isinstance(second, str):
                    computed = '(' + str(first) + '%' + second + ')'
                else:
                    # computed = '0x{:x}'.format(int(first / second))
                    computed = '(' + str(first) + '%' + str(second) + ')'

            # if isAllReal(first, second):
            #     if second == 0:
            #         computed = 0
            #     else:
            #         first = to_unsigned(first)
            #         second = to_unsigned(second)
            #         computed = first % second & UNSIGNED_BOUND_NUMBER

            # else:
            #     first = to_symbolic(first)
            #     second = to_symbolic(second)
            #
            #     solver.push()
            #     solver.add(Not(second == 0))
            #     if check_sat(solver) == unsat:
            #         # it is provable that second is indeed equal to zero
            #         computed = 0
            #     else:
            #         computed = URem(first, second)
            #     solver.pop()

            # computed = simplify(computed) if is_expr(computed) else computed
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "SMOD":
        if len(stack) > 1:
            global_state["pc"] += 1
            first = stack.pop(0)
            second = stack.pop(0)
            if isAllReal(first, second):
                if second == 0:
                    computed = 0
                else:
                    first = to_signed(first)
                    second = to_signed(second)
                    sign = -1 if first < 0 else 1
                    computed = sign * (abs(first) % abs(second))
            else:
                first = to_symbolic(first)
                second = to_symbolic(second)

                solver.push()
                solver.add(Not(second == 0))
                if check_sat(solver) == unsat:
                    # it is provable that second is indeed equal to zero
                    computed = 0
                else:

                    solver.push()
                    solver.add(first < 0) # check sign of first element
                    sign = BitVecVal(-1, 256) if check_sat(solver) == sat \
                        else BitVecVal(1, 256)
                    solver.pop()

                    z3_abs = lambda x: If(x >= 0, x, -x)
                    first = z3_abs(first)
                    second = z3_abs(second)

                    computed = sign * (first % second)
                solver.pop()

            computed = simplify(computed) if is_expr(computed) else computed
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "ADDMOD":
        if len(stack) > 2:
            global_state["pc"] += 1
            first = stack.pop(0)
            second = stack.pop(0)
            third = stack.pop(0)

            if isAllReal(first, second, third):
                if third == 0:
                    computed = 0
                else:
                    computed = (first + second) % third
            else:
                first = to_symbolic(first)
                second = to_symbolic(second)
                solver.push()
                solver.add( Not(third == 0) )
                if check_sat(solver) == unsat:
                    computed = 0
                else:
                    first = ZeroExt(256, first)
                    second = ZeroExt(256, second)
                    third = ZeroExt(256, third)
                    computed = (first + second) % third
                    computed = Extract(255, 0, computed)
                solver.pop()
            computed = simplify(computed) if is_expr(computed) else computed
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "MULMOD":
        if len(stack) > 2:
            global_state["pc"] += 1
            first = stack.pop(0)
            second = stack.pop(0)
            third = stack.pop(0)

            if isAllReal(first, second, third):
                if third == 0:
                    computed = 0
                else:
                    computed = (first * second) % third
            else:
                first = to_symbolic(first)
                second = to_symbolic(second)
                solver.push()
                solver.add( Not(third == 0) )
                if check_sat(solver) == unsat:
                    computed = 0
                else:
                    first = ZeroExt(256, first)
                    second = ZeroExt(256, second)
                    third = ZeroExt(256, third)
                    computed = URem(first * second, third)
                    computed = Extract(255, 0, computed)
                solver.pop()
            computed = simplify(computed) if is_expr(computed) else computed
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "EXP":
        if len(stack) > 1:
            # global_state["pc"] += 1
            base = stack.pop(0)
            exponent = stack.pop(0)
            # Type conversion is needed when they are mismatched
            computed = 0
            if isAllReal(base, exponent):
                computed = pow(base, exponent, 2**256)
                stack.insert(0, computed)
                if computed == 0:
                    return 10, 'no'
                else:
                    return 10+(10*(1+math.log(computed, 256))), 'no'
            else:
                # The computed value is unknown, this is because power is
                # not supported in bit-vector theory

                # new_var_name = gen.gen_arbitrary_var()
                # computed = BitVec(new_var_name, 256)

                # try:
                #     base = int(base, 16)
                # except:
                #     base = base
                # try:
                #     exponent = int(exponent, 16)
                # except:
                #     exponent = exponent
                if isinstance(base, str):
                    computed = '(' + base + '/' + str(exponent) + ')'
                elif isinstance(exponent, str):
                    computed = '(' + str(base) + '**' + exponent + ')'
                stack.insert(0, computed)
                return '10+(10*(1+log256({})))'.format(computed), 'no'
                # else:
                #     # computed = '0x{:x}'.format(int(pow(base, exponent, 2**256)))
                #     computed = simplify(computed) if is_expr(computed) else computed

        else:
            raise ValueError('STACK underflow')
    elif opcode == "SIGNEXTEND":
        if len(stack) > 1:
            global_state["pc"] += 1
            first = stack.pop(0)
            second = stack.pop(0)
            if isAllReal(first, second):
                if first >= 32 or first < 0:
                    computed = second
                else:
                    signbit_index_from_right = 8 * first + 7
                    if second & (1 << signbit_index_from_right):
                        computed = second | (2 ** 256 - (1 << signbit_index_from_right))
                    else:
                        computed = second & ((1 << signbit_index_from_right) - 1 )
            else:
                first = to_symbolic(first)
                second = to_symbolic(second)
                solver.push()
                solver.add( Not( Or(first >= 32, first < 0 ) ) )
                if check_sat(solver) == unsat:
                    computed = second
                else:
                    signbit_index_from_right = 8 * first + 7
                    solver.push()
                    solver.add(second & (1 << signbit_index_from_right) == 0)
                    if check_sat(solver) == unsat:
                        computed = second | (2 ** 256 - (1 << signbit_index_from_right))
                    else:
                        computed = second & ((1 << signbit_index_from_right) - 1)
                    solver.pop()
                solver.pop()
            computed = simplify(computed) if is_expr(computed) else computed
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    #
    #  10s: Comparison and Bitwise Logic Operations
    #
    elif opcode == "LT":
        computed = 0
        if len(stack) > 1:
            # global_state["pc"] += 1
            first = stack.pop(0)
            second = stack.pop(0)
            if isinstance(first, int) and isinstance(second, int):
                first = to_unsigned(first)
                second = to_unsigned(second)
                if first < second:
                    computed = 1
                else:
                    computed = 0
            else:
                if isinstance(first, str):
                    try:
                        first = int(first)
                    except ValueError:
                        first = first
                if isinstance(second, str):
                    # tmp = second.split('0x')
                    # if len(tmp) > 1:
                    #     second = int(second, 16)
                    # else:
                    #     second = second
                    try:
                        second = int(second)
                    except ValueError:
                        second = second
                if isinstance(first, int) and isinstance(second, int):
                    first = to_unsigned(first)
                    second = to_unsigned(second)
                    if first < second:
                        computed = 1
                    else:
                        computed = 0
                else:
                    computed = '(' + str(first) + '<' + str(second) + ')'
                # computed = '(' + str(first) + '<' + str(second) + ')'
            # else:
            #     computed = If(ULT(first, second), BitVecVal(1, 256), BitVecVal(0, 256))
            # computed = simplify(computed) if is_expr(computed) else computed
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "GT":
        if len(stack) > 1:
            global_state["pc"] += 1
            first = stack.pop(0)
            second = stack.pop(0)
            if isinstance(first, int) and isinstance(second, int):
                first = to_unsigned(first)
                second = to_unsigned(second)
                if first > second:
                    computed = 1
                else:
                    computed = 0
            else:
                # if isinstance(first, str):
                #     tmp = first.split('0x')
                #     if len(tmp) > 1:
                #         first = int(first, 16)
                #     else:
                #         first = first
                # if isinstance(second, str):
                #     tmp = second.split('0x')
                #     if len(tmp) > 1:
                #         second = int(second, 16)
                #     else:
                #         second = second
                if isinstance(first, int) and isinstance(second, int):
                    first = to_unsigned(first)
                    second = to_unsigned(second)
                    if first > second:
                        computed = 1
                    else:
                        computed = 0
                else:
                    computed = '(' + str(first) + '>' + str(second) + ')'
            #     computed = If(UGT(first, second), BitVecVal(1, 256), BitVecVal(0, 256))
            # computed = simplify(computed) if is_expr(computed) else computed
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "SLT":  # Not fully faithful to signed comparison
        if len(stack) > 1:
            global_state["pc"] += 1
            first = stack.pop(0)
            second = stack.pop(0)
            if isinstance(first, int) and isinstance(second, int):
                first = to_signed(first)
                second = to_signed(second)
                if first < second:
                    computed = 1
                else:
                    computed = 0
            else:
                computed = '(' + str(first) + '<' + str(second) + ')'
            #     computed = If(first < second, BitVecVal(1, 256), BitVecVal(0, 256))
            # computed = simplify(computed) if is_expr(computed) else computed
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "SGT":  # Not fully faithful to signed comparison
        if len(stack) > 1:
            global_state["pc"] += 1
            first = stack.pop(0)
            second = stack.pop(0)
            if isinstance(first, int) and isinstance(second, int):
                first = to_signed(first)
                second = to_signed(second)
                if first > second:
                    computed = 1
                else:
                    computed = 0
            else:
                computed = '(' + str(first) + '>' + str(second) + ')'
            #     computed = If(first > second, BitVecVal(1, 256), BitVecVal(0, 256))
            # computed = simplify(computed) if is_expr(computed) else computed
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "EQ":
        computed = 0
        if len(stack) > 1:
            # global_state["pc"] += 1
            first = stack.pop(0)
            second = stack.pop(0)
            if isinstance(first, int) and isinstance(second, int):
                if first == second:
                    computed = 1
                else:
                    computed = 0
            else:
                if isinstance(first, str):
                    computed = '(' + str(first) + '=' + str(second) + ')'
                elif isinstance(second, str):
                    computed = '(' + str(first) + '=' + str(second) + ')'
                else:
                    if first == second:
                        computed = 1
                    else:
                        computed = 0
                # computed = '(' + str(first) + '=' + str(second) + ')'
            # else:
            #     computed = If(first == second, BitVecVal(1, 256), BitVecVal(0, 256))
            # computed = simplify(computed) if is_expr(computed) else computed
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "ISZERO":
        # Tricky: this instruction works on both boolean and integer,
        # when we have a symbolic expression, type error might occur
        # Currently handled by try and catch
        computed = 0
        if len(stack) > 0:
            # global_state["pc"] += 1
            first = stack.pop(0)
            if isinstance(first, int):
                if first == 0:
                    computed = 1
                else:
                    computed = 0
            else:
                # try:
                #     first = int(first, 16)
                # except:
                #     first = first
                if isinstance(first, int):
                    if first == 0:
                        computed = 1
                    else:
                        computed = 0
                else:
                    computed = '(' + str(first) + '==0' + ')'
            # else:
            #     computed = If(first == 0, BitVecVal(1, 256), BitVecVal(0, 256))
            # computed = simplify(computed) if is_expr(computed) else computed
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "AND":
        if len(stack) > 1:
            # global_state["pc"] += 1
            first = stack.pop(0)
            second = stack.pop(0)
            if isinstance(first, int) and isinstance(second, int):
                computed = int(first) & second
            else:
                # if isinstance(first, str):
                #     try:
                #         first = int(first, 16)
                #     except:
                #         first = first
                #     # first = int(first, 16)
                # if isinstance(second, str):
                #     try:
                #         second = int(second, 16)
                #     except:
                #         second = second
                    # second = int(second, 16)
                # if isinstance(first, int) and isinstance(second, int):
                #     computed = '0x{:x}'.format(int(first & second))
                # else:
                computed = '(' + str(first) + '&' + str(second) + ')'
            # computed = simplify(computed) if is_expr(computed) else computed
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "OR":
        if len(stack) > 1:
            global_state["pc"] += 1
            first = stack.pop(0)
            second = stack.pop(0)

            if isinstance(first, int) and isinstance(second, int):
                computed = first | second
            else:
                computed = '(' + str(first) + '|' + str(second) + ')'
            # computed = simplify(computed) if is_expr(computed) else computed
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "XOR":
        if len(stack) > 1:
            global_state["pc"] += 1
            first = stack.pop(0)
            second = stack.pop(0)
            if isinstance(first, int) and isinstance(second, int):
                computed = first ^ second
            else:
                computed = str(first) + '^' + str(second)
            # computed = simplify(computed) if is_expr(computed) else computed
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "NOT":
        if len(stack) > 0:
            global_state["pc"] += 1
            first = stack.pop(0)
            if isinstance(first, int):
                computed = (~first) & UNSIGNED_BOUND_NUMBER
            else:
                computed = '(' + '~' + str(first) + ')'
            # computed = simplify(computed) if is_expr(computed) else computed
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "BYTE":
        if len(stack) > 1:
            global_state["pc"] += 1
            first = stack.pop(0)
            byte_index = 32 - first - 1
            second = stack.pop(0)

            if isAllReal(first, second):
                if first >= 32 or first < 0:
                    computed = 0
                else:
                    computed = second & (255 << (8 * byte_index))
                    computed >>= (8 * byte_index)
            else:
                first = to_symbolic(first)
                second = to_symbolic(second)
                solver.push()
                solver.add( Not (Or( first >= 32, first < 0 ) ) )
                if check_sat(solver) == unsat:
                    computed = 0
                else:
                    computed = second & (255 << (8 * byte_index))
                    computed >>= (8 * byte_index)
                solver.pop()
            computed = simplify(computed) if is_expr(computed) else computed
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    #
    # 20s: SHA3
    #
    elif opcode == "SHA3" or opcode == 'KECCAK256':
        if len(stack) > 1:
            # global_state["pc"] += 1
            s0 = stack.pop(0)
            s1 = stack.pop(0)
            # print('s0= ', s0)
            # print('s1= ', s1)
            if isinstance(s0, str):
                gas = '30+6*' + str(s0)
            elif isinstance(s0, int):
                gas = 30 + 6*s0
            else:
                gas = '30+6*' + str(s0)
            if isinstance(s0, int) and isinstance(s1, int):
                # print(s0, s1)
                # simulate the hashing of sha3
                # s0 = int(s0, 16)
                # s1 = int(s1, 16)
                data = [str(x) for x in memory[s0: s0 + s1]]
                position = ''.join(data)
                # print(position)
                # position = re.sub('[\s+]', '', position)
                # position = zlib.compress(six.b(position), 9)
                # position = base64.b64encode(position)
                # position = position.decode('utf-8', 'strict')
                computed = sha3.sha3_224(position.encode('utf-8')).hexdigest()
                stack.insert(0, computed)
                # if position in sha3_list:
                #     stack.insert(0, sha3_list[position])
                # else:
                #     new_var_name = gen.gen_arbitrary_var()
                #     new_var = BitVec(new_var_name, 256)
                #     sha3_list[position] = new_var
                #     stack.insert(0, new_var)
            # else:
            #     # push into the execution a fresh symbolic variable
            #     new_var_name = gen.gen_arbitrary_var()
            #     new_var = BitVec(new_var_name, 256)
            #     path_conditions_and_vars[new_var_name] = new_var
            #     stack.insert(0, new_var)
            return gas, 'no'
        else:
            raise ValueError('STACK underflow')
    #
    # 30s: Environment Information
    #
    elif opcode == "ADDRESS":  # get address of currently executing account
        global_state["pc"] += 1
        stack.insert(0, path_conditions_and_vars["Ia"])

    elif opcode == "BALANCE":
        if len(stack) > 0:
            global_state["pc"] += 1
            address = stack.pop(0)
            if isReal(address) and global_params.USE_GLOBAL_BLOCKCHAIN:
                new_var = data_source.getBalance(address)
            else:
                new_var_name = gen.gen_balance_var()
                if new_var_name in path_conditions_and_vars:
                    new_var = path_conditions_and_vars[new_var_name]
                else:
                    new_var = BitVec(new_var_name, 256)
                    path_conditions_and_vars[new_var_name] = new_var
            if isReal(address):
                hashed_address = "concrete_address_" + str(address)
            else:
                hashed_address = str(address)
            global_state["balance"][hashed_address] = new_var
            stack.insert(0, new_var)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "CALLER":  # get caller address
        # that is directly responsible for this execution
        # global_state["pc"] += 1
        stack.insert(0, str(global_state["sender_address"]))
    # elif opcode == "ORIGIN":  # get execution origination address
    #     global_state["pc"] += 1
    #     stack.insert(0, global_state["origin"])
    elif opcode == "CALLVALUE":  # get value of this transaction
        # global_state["pc"] += 1
        new_var = 0
        # 'wei with calldata'
        stack.insert(0, new_var) # global_state["value"])
    elif opcode == "CALLDATALOAD":  # from input data from environment
        if len(stack) > 0:
            # global_state["pc"] += 1
            # if g_src_map:
            #     source_code = g_src_map.get_source_code(global_state['pc'] - 1)
            #     if source_code.startswith("function") and isReal(position) and current_func_name in g_src_map.func_name_to_params:
            #         params = g_src_map.func_name_to_params[current_func_name]
            #         param_idx = (position - 4) // 32
            #         for param in params:
            #             if param_idx == param['position']:
            #                 new_var_name = param['name']
            #                 g_src_map.var_names.append(new_var_name)
            #     else:
            # new_var_name = gen.gen_data_var(position)
            # else:
            #     new_var_name = gen.gen_data_var(position)
            # if new_var_name in path_conditions_and_vars:
            #     new_var = path_conditions_and_vars[new_var_name]
            # else:
            # new_var = BitVec(new_var_name, 256)
            # path_conditions_and_vars[new_var_name] = new_var

            if len(input_data) > 0:
                stack.pop(0)
                data = input_data.pop(0)
                count = 64 - len(data)
                while count > 0:
                    data += '0'
                    count -= 1
                new_var = '0x' + data
                # new_var = int.from_bytes(input_data.pop(0), byteorder='big')
            else:
                position = stack.pop(0)
                new_var = 'Parameter'
            # new_var = 0
            stack.insert(0, new_var)
    #     else:
    #         raise ValueError('STACK underflow')
    elif opcode == "CALLDATASIZE":
        # global_state["pc"] += 1

        # new_var_name = gen.gen_data_size()
        # new_var = 'CALLDATASIZE' #path_conditions_and_vars[new_var_name]
        # new_var = 0
        #
        # if new_var_name in path_conditions_and_vars:
        #     new_var = path_conditions_and_vars[new_var_name]
        # else:
        # new_var = BitVec(new_var_name, 256)
        # path_conditions_and_vars[new_var_name] = new_var
        if input_data != '':
            new_var = 20
        else:
            new_var = 'size(calldata)'
        stack.insert(0, new_var)
    elif opcode == "CALLDATACOPY":  # Copy input data to memory
        #  TODO: Don't know how to simulate this yet
        if len(stack) > 2:
            # global_state["pc"] += 1
            z = stack.pop(0)
            y = stack.pop(0)
            x = stack.pop(0)
            if isinstance(z, str):
                gas = '2+3*' + z
            else:
                gas = 2 + 3*z
            return gas, 'no'
        else:
            raise ValueError('STACK underflow')
    elif opcode == "CODESIZE":
        # if g_disasm_file.endswith('.disasm'):
        #     evm_file_name = g_disasm_file[:-7]
        # else:
        #     evm_file_name = g_disasm_file
        # with open(evm_file_name, 'r') as evm_file:
        #     evm = evm_file.read()[:-1]
        #     code_size = len(evm)/2
        stack.insert(0, 'code_size')
    elif opcode == "CODECOPY":
        if len(stack) > 2:
            global_state["pc"] += 1
            mem_location = stack.pop(0)
            code_from = stack.pop(0)
            no_bytes = stack.pop(0)
            # current_miu_i = global_state["miu_i"]
            #
            # if isAllReal(mem_location, current_miu_i, code_from, no_bytes):
            #     if six.PY2:
            #         temp = long(math.ceil((mem_location + no_bytes) / float(32)))
            #     else:
            #         temp = int(math.ceil((mem_location + no_bytes) / float(32)))
            #
            #     if temp > current_miu_i:
            #         current_miu_i = temp
            #
            #     if g_disasm_file.endswith('.disasm'):
            #         evm_file_name = g_disasm_file[:-7]
            #     else:
            #         evm_file_name = g_disasm_file
            #     with open(evm_file_name, 'r') as evm_file:
            #         evm = evm_file.read()[:-1]
            #         start = code_from * 2
            #         end = start + no_bytes * 2
            #         code = evm[start: end]
            #     mem[mem_location] = int(code, 16)
            # else:
            #     new_var_name = gen.gen_code_var("Ia", code_from, no_bytes)
            #     if new_var_name in path_conditions_and_vars:
            #         new_var = path_conditions_and_vars[new_var_name]
            #     else:
            #         new_var = BitVec(new_var_name, 256)
            #         path_conditions_and_vars[new_var_name] = new_var
            #
            #     temp = ((mem_location + no_bytes) / 32) + 1
            #     current_miu_i = to_symbolic(current_miu_i)
            #     expression = current_miu_i < temp
            #     solver.push()
            #     solver.add(expression)
            #     if MSIZE:
            #         if check_sat(solver) != unsat:
            #             current_miu_i = If(expression, temp, current_miu_i)
            #     solver.pop()
            #     mem.clear() # very conservative
            #     mem[str(mem_location)] = new_var
            # global_state["miu_i"] = current_miu_i
        else:
            raise ValueError('STACK underflow')
    elif opcode == "RETURNDATACOPY":
        if len(stack) > 2:
            global_state["pc"] += 1
            stack.pop(0)
            stack.pop(0)
            z = stack.pop(0)
            # print(z)
            if isinstance(z, int):
                gas = 2 + 3 * int(z)
            else:
                gas = '2+3*'+z
            return gas, 'no'
        else:
            raise ValueError('STACK underflow')
    elif opcode == "RETURNDATASIZE":
        global_state["pc"] += 1
        # new_var_name = gen.gen_arbitrary_var()
        # new_var = BitVec(new_var_name, 256)
        new_var = 'size(returndata)'
        stack.insert(0, new_var)
    # elif opcode == "GASPRICE":
    #     global_state["pc"] += 1
    #     stack.insert(0, global_state["gas_price"])
    # elif opcode == "EXTCODESIZE":
    #     if len(stack) > 0:
    #         global_state["pc"] += 1
    #         address = stack.pop(0)
    #         if isReal(address) and global_params.USE_GLOBAL_BLOCKCHAIN:
    #             code = data_source.getCode(address)
    #             stack.insert(0, len(code)/2)
    #         else:
    #             #not handled yet
    #             new_var_name = gen.gen_code_size_var(address)
    #             if new_var_name in path_conditions_and_vars:
    #                 new_var = path_conditions_and_vars[new_var_name]
    #             else:
    #                 new_var = BitVec(new_var_name, 256)
    #                 path_conditions_and_vars[new_var_name] = new_var
    #             stack.insert(0, new_var)
    #     else:
    #         raise ValueError('STACK underflow')
    # elif opcode == "EXTCODECOPY":
    #     if len(stack) > 3:
    #         global_state["pc"] += 1
    #         address = stack.pop(0)
    #         mem_location = stack.pop(0)
    #         code_from = stack.pop(0)
    #         no_bytes = stack.pop(0)
    #         current_miu_i = global_state["miu_i"]
    #
    #         if isAllReal(address, mem_location, current_miu_i, code_from, no_bytes) and USE_GLOBAL_BLOCKCHAIN:
    #             if six.PY2:
    #                 temp = long(math.ceil((mem_location + no_bytes) / float(32)))
    #             else:
    #                 temp = int(math.ceil((mem_location + no_bytes) / float(32)))
    #             if temp > current_miu_i:
    #                 current_miu_i = temp
    #
    #             evm = data_source.getCode(address)
    #             start = code_from * 2
    #             end = start + no_bytes * 2
    #             code = evm[start: end]
    #             mem[mem_location] = int(code, 16)
    #         else:
    #             new_var_name = gen.gen_code_var(address, code_from, no_bytes)
    #             if new_var_name in path_conditions_and_vars:
    #                 new_var = path_conditions_and_vars[new_var_name]
    #             else:
    #                 new_var = BitVec(new_var_name, 256)
    #                 path_conditions_and_vars[new_var_name] = new_var
    #
    #             temp = ((mem_location + no_bytes) / 32) + 1
    #             current_miu_i = to_symbolic(current_miu_i)
    #             expression = current_miu_i < temp
    #             solver.push()
    #             solver.add(expression)
    #             if MSIZE:
    #                 if check_sat(solver) != unsat:
    #                     current_miu_i = If(expression, temp, current_miu_i)
    #             solver.pop()
    #             mem.clear() # very conservative
    #             mem[str(mem_location)] = new_var
    #         global_state["miu_i"] = current_miu_i
    #     else:
    #         raise ValueError('STACK underflow')
    # #
    # #  40s: Block Information
    # #
    # elif opcode == "BLOCKHASH":  # information from block header
    #     if len(stack) > 0:
    #         global_state["pc"] += 1
    #         stack.pop(0)
    #         new_var_name = "IH_blockhash"
    #         if new_var_name in path_conditions_and_vars:
    #             new_var = path_conditions_and_vars[new_var_name]
    #         else:
    #             new_var = BitVec(new_var_name, 256)
    #             path_conditions_and_vars[new_var_name] = new_var
    #         stack.insert(0, new_var)
    #     else:
    #         raise ValueError('STACK underflow')
    # elif opcode == "COINBASE":  # information from block header
    #     global_state["pc"] += 1
    #     stack.insert(0, global_state["currentCoinbase"])
    # elif opcode == "TIMESTAMP":  # information from block header
    #     global_state["pc"] += 1
    #     stack.insert(0, global_state["currentTimestamp"])
    elif opcode == "NUMBER":  # information from block header
        global_state["pc"] += 1
        stack.insert(0, 'currentNumber')
    # elif opcode == "DIFFICULTY":  # information from block header
    #     global_state["pc"] += 1
    #     stack.insert(0, global_state["currentDifficulty"])
    # elif opcode == "GASLIMIT":  # information from block header
    #     global_state["pc"] += 1
    #     stack.insert(0, global_state["currentGasLimit"])
    # #
    # #  50s: Stack, Memory, Storage, and Flow Information
    # #
    elif opcode == "POP":
        if len(stack) > 0:
            # global_state["pc"] += 1
            stack.pop(0)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "MLOAD":
        if len(stack) > 0:
            value = ''
            # global_state["pc"] += 1
            address = stack.pop(0)
            # current_miu_i = global_state["miu_i"]
            # if isAllReal(address, current_miu_i) and address in mem:
            #     if six.PY2:
            #         temp = long(math.ceil((address + 32) / float(32)))
            #     else:
            #         temp = int(math.ceil((address + 32) / float(32)))
            #     if temp > current_miu_i:
            #         current_miu_i = temp
            # print(stack)
            # print(address)
            # print(len(memory))
            # print(memory)
            try:
                address = int(address)
                value = memory[address]
            except:
                print(sym_mem)
                for i in sym_mem:
                    if address == i[0]:
                        value = i[1]

            stack.insert(0, value)
            # else:
            #     temp = ((address + 31) / 32) + 1
            #     current_miu_i = to_symbolic(current_miu_i)
            #     expression = current_miu_i < temp
            #     solver.push()
            #     solver.add(expression)
            #     if MSIZE:
            #         if check_sat(solver) != unsat:
            #             # this means that it is possibly that current_miu_i < temp
            #             current_miu_i = If(expression,temp,current_miu_i)
            #     solver.pop()
            #     new_var_name = gen.gen_mem_var(address)
            #     if new_var_name in path_conditions_and_vars:
            #         new_var = path_conditions_and_vars[new_var_name]
            #     else:
            #         new_var = BitVec(new_var_name, 256)
            #         path_conditions_and_vars[new_var_name] = new_var
            #     stack.insert(0, new_var)
            #     if isReal(address):
            #         mem[address] = new_var
            #     else:
            #         mem[str(address)] = new_var
            # global_state["miu_i"] = current_miu_i
        else:
            raise ValueError('STACK underflow')
    elif opcode == "MSTORE":
        if len(stack) > 1:
            # global_state["pc"] += 1
            stored_address = stack.pop(0)
            stored_value = stack.pop(0)
            # current_miu_i = global_state["miu_i"]
            # if isinstance(stored_address, str) and isinstance(stored_value, str):

            # print(stored_address, stored_value)
            try:
                stored_address = int(stored_address)
            except (TypeError, ValueError):
                stored_address = stored_address
            try:
                stored_value = int(stored_value)
            except (TypeError, ValueError):
                stored_value = stored_value

            if isinstance(stored_address, str):
                sym_mem.append((stored_address, stored_value))
            elif isinstance(stored_address, int):
                # preparing data for hashing later
                old_size = len(memory) // 32
                # print(old_size)
                new_size = ceil32(stored_address + 32) // 32
                # print(new_size)
                mem_extend = (new_size - old_size) * 32
                memory.extend([0] * mem_extend)
                value = stored_value
                for i in range(31, -1, -1):
                    memory[stored_address + i] = value
            else:
                sym_mem.append((str(stored_address), stored_value))
            # print('memory = ', memory)

            # if isAllReal(stored_address, current_miu_i):
            #     if six.PY2:
            #         temp = long(math.ceil((stored_address + 32) / float(32)))
            #     else:
            #         temp = int(math.ceil((stored_address + 32) / float(32)))
            #     if temp > current_miu_i:
            #         current_miu_i = temp
            #     mem[stored_address] = stored_value  # note that the stored_value could be symbolic
            # else:
            #     temp = ((stored_address + 31) / 32) + 1
            #     expression = current_miu_i < temp
            #     solver.push()
            #     solver.add(expression)
            #     if MSIZE:
            #         if check_sat(solver) != unsat:
            #             # this means that it is possibly that current_miu_i < temp
            #             current_miu_i = If(expression,temp,current_miu_i)
            #     solver.pop()
            #     mem.clear()  # very conservative
            #     mem[str(stored_address)] = stored_value
            # global_state["miu_i"] = current_miu_i
        else:
            raise ValueError('STACK underflow')
    # elif opcode == "MSTORE8":
    #     if len(stack) > 1:
    #         global_state["pc"] += 1
    #         stored_address = stack.pop(0)
    #         temp_value = stack.pop(0)
    #         stored_value = temp_value % 256  # get the least byte
    #         current_miu_i = global_state["miu_i"]
    #         if isAllReal(stored_address, current_miu_i):
    #             if six.PY2:
    #                 temp = long(math.ceil((stored_address + 1) / float(32)))
    #             else:
    #                 temp = int(math.ceil((stored_address + 1) / float(32)))
    #             if temp > current_miu_i:
    #                 current_miu_i = temp
    #             mem[stored_address] = stored_value  # note that the stored_value could be symbolic
    #         else:
    #             temp = (stored_address / 32) + 1
    #             if isReal(current_miu_i):
    #                 current_miu_i = BitVecVal(current_miu_i, 256)
    #             expression = current_miu_i < temp
    #             solver.push()
    #             solver.add(expression)
    #             if MSIZE:
    #                 if check_sat(solver) != unsat:
    #                     # this means that it is possibly that current_miu_i < temp
    #                     current_miu_i = If(expression,temp,current_miu_i)
    #             solver.pop()
    #             mem.clear()  # very conservative
    #             mem[str(stored_address)] = stored_value
    #         global_state["miu_i"] = current_miu_i
    #     else:
    #         raise ValueError('STACK underflow')
    elif opcode == "SLOAD":
        if len(stack) > 0:
            # global_state["pc"] += 1
            position = stack.pop(0)
            # print("position = ", position)
            value = 0
            # print('storage', storage)
            for s in storage:
                if s[0] == position:
                    value = s[1]
            # if isReal(position) and position in global_state["Ia"]:
            #     value = global_state["Ia"][position]
            stack.insert(0, value)
            # elif global_params.USE_GLOBAL_STORAGE and isReal(position) and position not in global_state["Ia"]:
            #     value = data_source.getStorageAt(position)
            #     global_state["Ia"][position] = value
            #     stack.insert(0, value)
            # else:
            #     if str(position) in global_state["Ia"]:
            #         value = global_state["Ia"][str(position)]
            #         stack.insert(0, value)
            #     else:
            #         if is_expr(position):
            #             position = simplify(position)
            #         if g_src_map:
            #             new_var_name = g_src_map.get_source_code(global_state['pc'] - 1)
            #             operators = '[-+*/%|&^!><=]'
            #             new_var_name = re.compile(operators).split(new_var_name)[0].strip()
            #             new_var_name = g_src_map.get_parameter_or_state_var(new_var_name)
            #             if new_var_name:
            #                 new_var_name = "Ia_store" + "-" + str(position) + "-" + new_var_name
            #             else:
            #                 new_var_name = gen.gen_owner_store_var(position)
            #         else:
            #             new_var_name = gen.gen_owner_store_var(position)
            #
            #         if new_var_name in path_conditions_and_vars:
            #             new_var = path_conditions_and_vars[new_var_name]
            #         else:
            #             new_var = BitVec(new_var_name, 256)
            #             path_conditions_and_vars[new_var_name] = new_var
            #         stack.insert(0, new_var)
            #         if isReal(position):
            #             global_state["Ia"][position] = new_var
            #         else:
            #             global_state["Ia"][str(position)] = new_var
        else:
            raise ValueError('STACK underflow')

    elif opcode == "SSTORE":
        if len(stack) > 1:
            # for call_pc in calls:
            #     calls_affect_state[call_pc] = True
            # global_state["pc"] += 1
            stored_address = stack.pop(0)
            stored_value = stack.pop(0)
            storage.append((stored_address, stored_value))

            if not stored_value == 0 and stored_address == 0:
                gas = 20000
            else:
                gas = 5000

            # if isReal(stored_address):
            #     # note that the stored_value could be unknown
            #     global_state["Ia"][stored_address] = stored_value
            # else:
            #     # note that the stored_value could be unknown
            #     global_state["Ia"][str(stored_address)] = stored_value
            return gas, 'no'
        else:
            raise ValueError('STACK underflow')
    elif opcode == "JUMP":
        if len(stack) > 0:
            target_address = stack.pop(0)
            # if isSymbolic(target_address):
            #     try:
            #         target_address = int(str(simplify(target_address)))
            #     except:
            #         raise TypeError("Target address must be an integer")
            # vertices[block].set_jump_target(target_address)
            # if target_address not in edges[block]:
            #     edges[block].append(target_address)
            jumpdest = target_address
            # print('jump = ', jumpdest)
        else:
            raise ValueError('STACK underflow')
    elif opcode == "JUMPI":
        # We need to prepare two branches
        if len(stack) > 1:
            target_address = stack.pop(0)
            # if isSymbolic(target_address):
            #     try:
            #         target_address = int(str(simplify(target_address)))
            #     except:
            #         raise TypeError("Target address must be an integer")
            # vertices[block].set_jump_target(target_address)
            flag = stack.pop(0)
            # branch_expression = False
            # if isReal(flag):
            #     if flag != 0:
            #         branch_expression = True
            # else:
            #     branch_expression = (flag != 0)
            # vertices[block].set_branch_expression(branch_expression)
            # if target_address not in edges[block]:
            #     edges[block].append(target_address)
            if flag == 1:
                return 1, target_address
            elif flag == 0:
                return 0, target_address
            else:
                t_constraint.append(flag+'==1')
                f_constraint.append(flag+'==0')
                # t_constraint = flag + '==1'
                # f_constraint = flag + '==0'
                # solve()
                # print('False constraint = ', f_constraint)
                # print('True constraint = ', t_constraint)
                return flag, target_address
        else:
            raise ValueError('STACK underflow')
    # elif opcode == "PC":
    #     stack.insert(0, global_state["pc"])
    #     global_state["pc"] += 1
    # elif opcode == "MSIZE":
    #     global_state["pc"] += 1
    #     msize = 32 * global_state["miu_i"]
    #     stack.insert(0, msize)
    elif opcode == "GAS":
        # In general, we do not have this precisely. It depends on both
        # the initial gas and the amount has been depleted
        # we need o think about this in the future, in case precise gas
        # can be tracked
        # global_state["pc"] += 1
        # new_var_name = gen.gen_gas_var()
        # new_var = BitVec(new_var_name, 256)
        # path_conditions_and_vars[new_var_name] = new_var
        new_var = 'GasAvaliable'
        stack.insert(0, new_var)
    elif opcode == "JUMPDEST":
        # Literally do nothing
        global_state["pc"] += 1
        # print('JUMPDEST')
    #
    #  60s & 70s: Push Operations
    #
    elif opcode.startswith('PUSH', 0):  # this is a push instruction
        # position = int(opcode[4:], 10)
        # global_state["pc"] = global_state["pc"] + 1 + position
        pushed_value = ''
        # print(instr_parts)
        if instr_parts[1] == '[tag]':
            pushed_value = int(instr_parts[2])
        else:
            try:
                pushed_value = int(instr_parts[1])
            except ValueError:
                if len(instr_parts[1]) > 4:
                    pushed_value = str(instr_parts[1])
                elif instr_parts[1] == 'data':
                    if len(instr_parts[1]) > 4:
                        pushed_value = str(instr_parts[2])
                else:
                    pushed_value = int(instr_parts[1], 16)

            # if len(instr_parts[1]) > 10:
            #     count = 64 - len(instr_parts[1])
            #     pushed_value = instr_parts[1]
            #     while count > 0:
            #         pushed_value = '0' + pushed_value
            #         count -= 1
            #     pushed_value = '0x{}'.format(pushed_value)
            # else:
            #     pushed_value = '0x{:x}'.format(int(instr_parts[1], 16))
                # hex(int(instr_parts[1], 16)).split('0x')[1]
        stack.insert(0, pushed_value)

        # if global_params.UNIT_TEST == 3: # test evm symbolic
        #     stack[0] = BitVecVal(stack[0], 256)
    #
    # #  80s: Duplication Operations
    #
    elif opcode.startswith("DUP", 0):
        # global_state["pc"] += 1
        position = int(opcode[3:], 10) - 1
        if len(stack) > position:
            duplicate = stack[position]
            stack.insert(0, duplicate)
        else:
            raise ValueError('STACK underflow')

    #
    #  90s: Swap Operations
    #
    elif opcode.startswith("SWAP", 0):
        # global_state["pc"] += 1
        position = int(opcode[4:], 10)
        if len(stack) > position:
            temp = stack[position]
            stack[position] = stack[0]
            stack[0] = temp
        else:
            raise ValueError('STACK underflow')

    #
    # #  a0s: Logging Operations
    # #
    elif opcode in ("LOG0", "LOG1", "LOG2", "LOG3", "LOG4"):
        # global_state["pc"] += 1
        # We do not simulate these log operations
        num_of_pops = 2 + int(opcode[3:])
        count = 0
        gas = 0
        while num_of_pops > 0:
            l = stack.pop(0)
            num_of_pops -= 1
            if count == 1:
                # print(l)
                if isinstance(l, str):
                    gas = str((int(opcode[3:]) + 1) * 375) + '+(8*' + l + ')'
                else:
                    gas = (int(opcode[3:]) + 1) * 375 + (8 * l)
            count += 1
        return gas, 'no'
    #
    # #
    # #  f0s: System Operations
    # #
    # elif opcode == "CREATE":
    #     if len(stack) > 2:
    #         global_state["pc"] += 1
    #         stack.pop(0)
    #         stack.pop(0)
    #         stack.pop(0)
    #         new_var_name = gen.gen_arbitrary_var()
    #         new_var = BitVec(new_var_name, 256)
    #         stack.insert(0, new_var)
    #     else:
    #         raise ValueError('STACK underflow')
    elif opcode == "CALL":
        # TODO: Need to handle miu_i
        if len(stack) > 6:
            # calls.append(global_state["pc"])
            # for call_pc in calls:
            #     if call_pc not in calls_affect_state:
            #         calls_affect_state[call_pc] = False
            # global_state["pc"] += 1
            outgas = stack.pop(0)
            recipient = stack.pop(0)
            transfer_amount = stack.pop(0)
            start_data_input = stack.pop(0)
            size_data_input = stack.pop(0)
            start_data_output = stack.pop(0)
            size_data_ouput = stack.pop(0)
            # in the paper, it is shaky when the size of data output is
            # min of stack[6] and the | o |

            if isReal(transfer_amount):
                if transfer_amount == 0:
                    stack.insert(0, 1)   # x = 0

            # Let us ignore the call depth
            # balance_ia = global_state["balance"]["Ia"]
            # is_enough_fund = (transfer_amount <= balance_ia)
            # solver.push()
            # solver.add(is_enough_fund)
            #
            # if check_sat(solver) == unsat:
            #     # this means not enough fund, thus the execution will result in exception
            #     solver.pop()
            #     stack.insert(0, 0)   # x = 0
            # else:
            #     # the execution is possibly okay
            #     stack.insert(0, 1)   # x = 1
            #     solver.pop()
            #     solver.add(is_enough_fund)
            #     path_conditions_and_vars["path_condition"].append(is_enough_fund)
            #     last_idx = len(path_conditions_and_vars["path_condition"]) - 1
            #     analysis["time_dependency_bug"][last_idx] = global_state["pc"] - 1
            #     new_balance_ia = (balance_ia - transfer_amount)
            #     global_state["balance"]["Ia"] = new_balance_ia
            #     address_is = path_conditions_and_vars["Is"]
            #     address_is = (address_is & CONSTANT_ONES_159)
            #     boolean_expression = (recipient != address_is)
            #     solver.push()
            #     solver.add(boolean_expression)
            #     if check_sat(solver) == unsat:
            #         solver.pop()
            #         new_balance_is = (global_state["balance"]["Is"] + transfer_amount)
            #         global_state["balance"]["Is"] = new_balance_is
            #     else:
            #         solver.pop()
            #         if isReal(recipient):
            #             new_address_name = "concrete_address_" + str(recipient)
            #         else:
            #             new_address_name = gen.gen_arbitrary_address_var()
            #         old_balance_name = gen.gen_arbitrary_var()
            #         old_balance = BitVec(old_balance_name, 256)
            #         path_conditions_and_vars[old_balance_name] = old_balance
            #         constraint = (old_balance >= 0)
            #         solver.add(constraint)
            #         path_conditions_and_vars["path_condition"].append(constraint)
            #         new_balance = (old_balance + transfer_amount)
            #         global_state["balance"][new_address_name] = new_balance
        else:
            raise ValueError('STACK underflow')
    # elif opcode == "CALLCODE":
    #     # TODO: Need to handle miu_i
    #     if len(stack) > 6:
    #         calls.append(global_state["pc"])
    #         for call_pc in calls:
    #             if call_pc not in calls_affect_state:
    #                 calls_affect_state[call_pc] = False
    #         global_state["pc"] += 1
    #         outgas = stack.pop(0)
    #         recipient = stack.pop(0) # this is not used as recipient
    #         if global_params.USE_GLOBAL_STORAGE:
    #             if isReal(recipient):
    #                 recipient = hex(recipient)
    #                 if recipient[-1] == "L":
    #                     recipient = recipient[:-1]
    #                 recipients.add(recipient)
    #             else:
    #                 recipients.add(None)
    #
    #         transfer_amount = stack.pop(0)
    #         start_data_input = stack.pop(0)
    #         size_data_input = stack.pop(0)
    #         start_data_output = stack.pop(0)
    #         size_data_ouput = stack.pop(0)
    #         # in the paper, it is shaky when the size of data output is
    #         # min of stack[6] and the | o |
    #
    #         if isReal(transfer_amount):
    #             if transfer_amount == 0:
    #                 stack.insert(0, 1)   # x = 0
    #                 return
    #
    #         # Let us ignore the call depth
    #         balance_ia = global_state["balance"]["Ia"]
    #         is_enough_fund = (transfer_amount <= balance_ia)
    #         solver.push()
    #         solver.add(is_enough_fund)
    #
    #         if check_sat(solver) == unsat:
    #             # this means not enough fund, thus the execution will result in exception
    #             solver.pop()
    #             stack.insert(0, 0)   # x = 0
    #         else:
    #             # the execution is possibly okay
    #             stack.insert(0, 1)   # x = 1
    #             solver.pop()
    #             solver.add(is_enough_fund)
    #             path_conditions_and_vars["path_condition"].append(is_enough_fund)
    #             last_idx = len(path_conditions_and_vars["path_condition"]) - 1
    #             analysis["time_dependency_bug"][last_idx] = global_state["pc"] - 1
    #     else:
    #         raise ValueError('STACK underflow')
    # elif opcode in ("DELEGATECALL", "STATICCALL"):
    #     if len(stack) > 5:
    #         global_state["pc"] += 1
    #         stack.pop(0)
    #         recipient = stack.pop(0)
    #         if global_params.USE_GLOBAL_STORAGE:
    #             if isReal(recipient):
    #                 recipient = hex(recipient)
    #                 if recipient[-1] == "L":
    #                     recipient = recipient[:-1]
    #                 recipients.add(recipient)
    #             else:
    #                 recipients.add(None)
    #
    #         stack.pop(0)
    #         stack.pop(0)
    #         stack.pop(0)
    #         stack.pop(0)
    #         new_var_name = gen.gen_arbitrary_var()
    #         new_var = BitVec(new_var_name, 256)
    #         stack.insert(0, new_var)
    #     else:
    #         raise ValueError('STACK underflow')
    elif opcode in ("RETURN", "REVERT"):
        # TODO: Need to handle miu_i
        if len(stack) > 1:
            global_state["pc"] += 1
            stack.pop(0)
            stack.pop(0)
            # TODO
            pass
        else:
            raise ValueError('STACK underflow')
    # elif opcode == "SUICIDE":
    #     global_state["pc"] += 1
    #     recipient = stack.pop(0)
    #     transfer_amount = global_state["balance"]["Ia"]
    #     global_state["balance"]["Ia"] = 0
    #     if isReal(recipient):
    #         new_address_name = "concrete_address_" + str(recipient)
    #     else:
    #         new_address_name = gen.gen_arbitrary_address_var()
    #     old_balance_name = gen.gen_arbitrary_var()
    #     old_balance = BitVec(old_balance_name, 256)
    #     path_conditions_and_vars[old_balance_name] = old_balance
    #     constraint = (old_balance >= 0)
    #     solver.add(constraint)
    #     path_conditions_and_vars["path_condition"].append(constraint)
    #     new_balance = (old_balance + transfer_amount)
    #     global_state["balance"][new_address_name] = new_balance
    #     # TODO
    #     return

    else:
        # log.debug("UNKNOWN INSTRUCTION: " + opcode)
        # if global_params.UNIT_TEST == 2 or global_params.UNIT_TEST == 3:
        #     # log.critical("Unknown instruction: %s" % opcode)
        #     # exit(UNKNOWN_INSTRUCTION)
        raise Exception('UNKNOWN INSTRUCTION: ' + opcode)

    return 'no', 'no'

if __name__ == '__main__':
    main()
