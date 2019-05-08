from z3 import *
import state_simulation


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

                if f_1.num_args() == f_2.num_args() and s_1.num_args() == s_2.num_args():
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


def unpack_if(expr):
    # print('[IF]:', expr, expr.decl())
    expr = state_simulation.numref_to_int(expr)
    if is_expr(expr) and str(expr.decl()) == 'If':
        # print('[IF-1]:', expr.arg(0))
        return unpack_if(expr.arg(0))
    else:
        # print('[IF-2]:', expr)
        return expr
