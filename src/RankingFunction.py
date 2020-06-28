from z3 import *
import src.settings as settings

class RankingFunction:

    def __init__(self):
        self.RankingFunctionConstraints = list()
        self.if_constraint = list()
        self.cfg_vars = list()
        self.cfg_pvars = list()
        self.cfg_constraint = list()

    def add_constraint(self, constraints: [BitVecRef], decl: str) -> None:
        replace_pattern = list()
        v = list()
        for constraint in constraints:
            variables, rp = self.get_z3_variable(constraint)
            replace_pattern += rp
            v += variables
            for variable in variables:
                if str(variable) not in self.cfg_vars:
                    self.cfg_vars.append(str(variable))
                    self.cfg_pvars.append(str(variable)+"'")
        rfc = RankingFunctionConstraint(constraints, decl, replace_pattern, v)
        self.RankingFunctionConstraints.append(rfc)

    def create_cfg(self):
        for rfc in self.RankingFunctionConstraints:
            c_prime = str(rfc.constraints[1])
            for v in self.cfg_vars:
                c_prime = c_prime.replace(v, v+"'")
            c = '%s = %s' % (c_prime, rfc.constraints[0])
            self.cfg_constraint.append(c)
            if rfc.decl == 'UGT':
                self.cfg_constraint.append('%s > 0' % rfc.constraints[0])
            elif rfc.decl == 'ULT':
                self.cfg_constraint.append('%s < 0' % rfc.constraints[0])
            else:
                raise Error('Ranking Function Error')
        self.__cfg_format()

    def get_z3_variable(self, constraint: BitVecRef) -> ([BitVecRef], [BitVecRef]):
        variables = list()
        replace_pattern = list()
        for e in self.__visitor(constraint, {}):
            if is_const(e) and e.decl().kind() == Z3_OP_UNINTERPRETED:
                variables.append(str(e))
            else:
                if str(e.decl()) == '&':
                    replace_pattern.append(str(e).replace('\n', '').replace(' ', ''))
                if str(e.decl()) == 'If' and e not in self.if_constraint:
                    self.if_constraint.append(e)
        return variables, replace_pattern

    def __visitor(self, e, seen):
        if e in seen:
            return
        seen[e] = True
        yield e
        if is_app(e):
            for ch in e.children():
                for e in self.__visitor(ch, seen):
                    yield e
            return
        if is_quantifier(e):
            for e in self.__visitor(e.body(), seen):
                yield e
            return

    def __cfg_format(self):
        self.cfg = '''
{
    vars: [%s],
    pvars: [%s],
    initnode: n0,
    nodes:{},
    transitions: [
        {
            source: n0,
            target: n0,
            name: t0,
            constraints: [%s]
        },
        {
            source: n0,
            target: n1,
            name: t1,
            constraints: [%s]
        },
    ]
}
        ''' % (','.join(self.cfg_vars), ','.join(self.cfg_pvars), ','.join(self.cfg_constraint), ','.join(["%s' = %s" % (x,x) for x in self.cfg_vars]))

    def render(self, name: str) -> None:
        with open('%s/%s/RankingFunciton/%s.fc' % (settings.OUTPUT_PATH, settings.CONTRACT_NAME, name), 'w') as f:
            f.write(self.cfg)

class RankingFunctionConstraint:

    def __init__(self, constraints: [BitVecRef], decl: str, replace_pattern: [BitVecRef], cfg_vars: [str]):
        self.decl = decl
        self.constraints = [str(constraint).replace('\n', '').replace(' ', '') for constraint in constraints]
        for pattern in replace_pattern:
            for c_idx in range(len(self.constraints)):
                if pattern in self.constraints[c_idx]:
                    for v in cfg_vars:
                        if v in pattern:
                            self.constraints[c_idx] = self.constraints[c_idx].replace(pattern, v)
