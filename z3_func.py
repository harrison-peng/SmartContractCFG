from z3 import *


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


def get_solver_var(s):
    vars_li = list()
    seen = {}
    for fml_imp in s.assertions():
        fml = fml_imp.children()[1]
        for e in visitor(fml, seen):
            if is_const(e) and e.decl().kind() == Z3_OP_UNINTERPRETED:
                vars_li.append(e)
    return vars_li
