from z3 import *
import asm_state_simulation


def loop_detection(ins_dict, prev_ins_dict):
    ins = ins_dict['ins']
    first = ins_dict['s1']
    second = ins_dict['s2']
    val = None
    prev_first = None
    prev_second = None

    if prev_ins_dict:
        prev_first_tem = simplify(prev_ins_dict['s1']) if is_expr(prev_ins_dict['s1']) else prev_ins_dict['s1']
        prev_second_tem = simplify(prev_ins_dict['s2']) if is_expr(prev_ins_dict['s2']) else prev_ins_dict['s2']
        prev_first = prev_first_tem if 'Extract' not in str(prev_first_tem) else prev_ins_dict['s1']
        prev_second = prev_second_tem if 'Extract' not in str(prev_second_tem) else prev_ins_dict['s2']
        prev_first = prev_first.as_long() if isinstance(prev_first, z3.z3.BitVecNumRef) else prev_first
        prev_second = prev_second.as_long() if isinstance(prev_second, z3.z3.BitVecNumRef) else prev_second

    if ((prev_first is not None and is_expr(prev_first)) or (prev_second is not None and is_expr(prev_second))) \
            and (is_expr(first) or is_expr(second)):
        # print(ins_dict, ':::', prev_ins_dict)
        val = dict()
        if ins not in ['LT', 'EQ', 'GT']:
            prev_first = prev_ins_dict['s1']
            first_tem = simplify(first)
            prev_first_tem = simplify(prev_first)
            if 'Extract' not in str(first_tem) and 'Extract' not in str(prev_first_tem):
                first = first_tem
                prev_first = prev_first_tem

            if str(first.decl()) == 'If':
                first_1 = unpack_if(first)
                prev_first_1 = unpack_if(prev_first)
                val['ins'] = ins
                val['op'] = first_1.decl()
                f_1 = first_1.arg(0)
                s_1 = first_1.arg(1)
                f_2 = prev_first_1.arg(0)
                s_2 = prev_first_1.arg(1)

                if f_1 == s_2 or f_2 == s_1:
                    f_2, s_2 = s_2, f_2

                if f_1.num_args() == f_2.num_args() or s_1.num_args() == s_2.num_args():
                    if f_1 == f_2:
                        if isinstance(s_1, z3.z3.BitVecNumRef):
                            s_1 = s_1.as_long()
                        if isinstance(s_2, z3.z3.BitVecNumRef):
                            s_2 = s_2.as_long()
                        val['diff'] = s_1 - s_2
                        val['var'] = f_1
                        val['var_position'] = 1
                    elif s_1 == s_2:
                        if isinstance(f_1, z3.z3.BitVecNumRef):
                            f_1 = f_1.as_long()
                        if isinstance(f_2, z3.z3.BitVecNumRef):
                            f_2 = f_2.as_long()
                        val['diff'] = f_1 - f_2
                        val['var'] = s_1
                        val['var_position'] = 2
                    else:
                        print('[ERR - 4.1]:', f_1, ',', s_1, ',', f_2, ',', s_2)
                        print('[ERR - 4.1]:', ins_dict, ',', prev_ins_dict)
                        raise ValueError('LOOP DETECTION ERROR - 4.1')
                elif f_1.num_args() == 0 and s_1.num_args() == 2 and f_2.num_args() == 0 and s_2.num_args() == 0:
                    s_1_1 = s_1.arg(0)
                    s_1_2 = s_1.arg(1)
                    if isinstance(s_1_1, z3.z3.BitVecRef) and s_1_1 == s_2:
                        val['var'] = s_1_1
                        val['diff'] = simplify(f_1 - s_1_2)
                        val['var_position'] = 2
                    elif isinstance(s_1_2, z3.z3.BitVecRef) and s_1_2 == s_2:
                        val['var'] = s_1_2
                        val['diff'] = simplify(f_1 - s_1_1)
                        val['var_position'] = 2
                    else:
                        print('[ERR - 4.2]:', f_2, ',', s_2, ',', f_1, ',', s_1_1, ',', s_1_2)
                        print('[ERR - 4.2]:', ins_dict, ',', prev_ins_dict)
                        raise ValueError('LOOP DETECTION ERROR - 4.2')
                else:
                    print('[ERR - 3]:', f_1.num_args(), s_1.num_args(), f_2.num_args(), s_2.num_args())
                    print('[ERR - 3]', f_1, ',', s_1, ',', f_2, ',', s_2)
                    raise ValueError('LOOP DETECTION ERROR - 3')
            else:
                raise ValueError('LOOP DETECTION ERROR - 2')
            return True, val
        else:
            val['ins'] = ins
            if is_expr(first) and is_expr(prev_first) and first == prev_first:
                val['diff'] = second - prev_second
            elif is_expr(second) and is_expr(prev_second) and second == prev_second:
                val['diff'] = first - prev_first
            else:
                raise ValueError('LOOP DETECTION ERROR - 1')
        return True, val
    else:
        return False, val


def handle_loop_condition(prev_jumpi_ins, loop_condition, addr, cons_val, new_var):
    if prev_jumpi_ins['ins'] == 'ISZERO':
        sym_var = cons_val['var']
        # gas_cons.add(state_simulation.add_gas_constraint(sym_var, UNSIGNED_BOUND_NUMBER))
        if str(cons_val['op']) == 'ULT':
            if cons_val['var_position'] == 1:
                loop_pc = simplify(If(Not(ULT(sym_var, cons_val['diff'] * new_var)), 1, 0))
            else:
                loop_pc = simplify(If(Not(ULT(cons_val['diff'] * new_var, sym_var)), 1, 0))
        elif str(cons_val['op']) == 'UGT':
            if cons_val['var_position'] == 1:
                loop_pc = simplify(If(Not(UGT(sym_var, cons_val['diff'] * new_var)), 1, 0))
            else:
                loop_pc = simplify(If(Not(UGT(cons_val['diff'] * new_var, sym_var)), 1, 0))
        elif str(cons_val['op']) == 'ULE':
            if cons_val['var_position'] == 1:
                loop_pc = simplify(If(Not(ULE(sym_var, cons_val['diff'] * new_var)), 1, 0))
            else:
                loop_pc = simplify(If(Not(ULE(cons_val['diff'] * new_var, sym_var)), 1, 0))
        elif str(cons_val['op']) == '==':
            loop_pc = simplify(If(Not(sym_var == cons_val['diff'] * new_var), 1, 0))
        else:
            print('[LOOp ERROR]:', cons_val)
            raise ValueError('LOOP INS ERROR - ISZERO')
    elif prev_jumpi_ins['ins'] in ['LT', 'EQ', 'GT']:
        if is_expr(prev_jumpi_ins['s1']) and prev_jumpi_ins['s1'] == loop_condition[addr]['s1']:
            sym_var = prev_jumpi_ins['s1']
            var_position = 1
        elif is_expr(prev_jumpi_ins['s2']) and prev_jumpi_ins['s2'] == loop_condition[addr]['s2']:
            sym_var = prev_jumpi_ins['s2']
            var_position = 2
        else:
            raise ValueError('LOOP SYM VAR ERROR - 328')

        if prev_jumpi_ins['ins'] == 'LT':
            if var_position == 1:
                loop_pc = simplify(If(ULT(sym_var, cons_val['diff'] * new_var), 1, 0))
            else:
                loop_pc = simplify(If(ULT(cons_val['diff'] * new_var, sym_var), 1, 0))
        elif prev_jumpi_ins['ins'] == 'GT':
            if var_position == 1:
                loop_pc = simplify(If(UGT(sym_var, cons_val['diff'] * new_var), 1, 0))
            else:
                loop_pc = simplify(If(UGT(cons_val['diff'] * new_var, sym_var), 1, 0))
        elif prev_jumpi_ins['ins'] == 'EQ':
            loop_pc = simplify(If(cons_val['diff'] * new_var == sym_var, 1, 0))
        else:
            raise ValueError('LOOP INS ERROR - OP')
    else:
        sym_var = BitVec(cons_val['var'], 256)
        # gas_cons.add(state_simulation.add_gas_constraint(sym_var, UNSIGNED_BOUND_NUMBER))
        if cons_val['op'] == 'ULT':
            if cons_val['var_position'] == 1:
                loop_pc = simplify(If(ULT(sym_var, cons_val['diff'] * new_var), 1, 0))
            else:
                loop_pc = simplify(If(ULT(cons_val['diff'] * new_var, sym_var), 1, 0))
        else:
            raise ValueError('LOOP INS ERROR - OTHER')
    return loop_pc


def unpack_if(expr):
    # print('[IF]:', expr, expr.decl())
    expr = asm_state_simulation.numref_to_int(expr)
    if is_expr(expr) and str(expr.decl()) == 'If':
        # print('[IF-1]:', expr.arg(0))
        return unpack_if(expr.arg(0))
    else:
        # print('[IF-2]:', expr)
        return expr
