from z3 import *
import six


def to_z3_symbolic(var):
    return BitVec(str(var), 256)


def to_unsigned(number):
    if number < 0:
        return number + 2**256
    return number


def to_signed(number):
    if number > 2**(256 - 1):
        return (2**256 - number) * (-1)
    else:
        return number


def is_symbolic(value):
    return not isinstance(value, six.integer_types)


def is_all_real(*args):
    for element in args:
        if is_symbolic(element):
            return False
    return True


def to_symbolic(number):
    if is_real(number):
        return BitVecVal(number, 256)
    return number


def is_real(value):
    return isinstance(value, six.integer_types)


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


def add_gas_constraint(formula, size):
    return simplify(ULT(formula, size))


def numref_to_int(expr):
    if isinstance(expr, z3.z3.BitVecNumRef):
        return expr.as_long()
    else:
        return expr


def visitor(e, seen):
    if e in seen:
        return
    seen[e] = True
    yield e
    if is_app(e):
        for ch in e.children():
            for e in visitor(ch, seen):
                yield e
        return
    if is_quantifier(e):
        for e in visitor(e.body(), seen):
            yield e
        return