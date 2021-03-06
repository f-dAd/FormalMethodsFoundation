import unittest
from typing import List
import copy
from z3 import *

# In this problem, you will implement the DPLL algorithm as discussed
# in the class.


# a utility class to represent the code you should fill in.
class Todo(Exception):
    def __init__(self, msg):
        self.msg = msg

    def __str__(self):
        return self.msg

    def __repr__(self):
        return self.__str__()


########################################
# This bunch of code declare the syntax for the propositional logic, we
# repeat here:
'''
P ::= p
    | T
    | F
    | P /\ P
    | P \/ P
    | P -> P
    | ~P
'''


class Prop:
    def __repr__(self):
        return self.__str__()


class PropVar(Prop):
    def __init__(self, var):
        self.var = var

    def __str__(self):
        return self.var

    def __hash__(self):
        return hash(self.var)

    def __eq__(self, other):
        return other.__class__ == self.__class__ and self.var == other.var


class PropTrue(Prop):
    def __init__(self):
        pass

    def __str__(self):
        return "True"

    def __eq__(self, other):
        return other.__class__ == self.__class__


class PropFalse(Prop):
    def __init__(self):
        pass

    def __str__(self):
        return "False"

    def __eq__(self, other):
        return other.__class__ == self.__class__


class PropAnd(Prop):
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __str__(self):
        return f"({self.left} /\\ {self.right})"


class PropOr(Prop):
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __str__(self):
        return f"({self.left} \\/ {self.right})"


class PropImplies(Prop):
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __str__(self):
        return f"({self.left} -> {self.right})"


class PropNot(Prop):
    def __init__(self, p):
        self.p = p

    def __str__(self):
        return f"~{self.p}"


# we can convert the above defined syntax into Z3's representation, so
# that we can check it's validity easily:
def to_z3(prop):
    if isinstance(prop, PropVar):
        return Bool(prop.var)
    if isinstance(prop, PropTrue):
        return prop
    if isinstance(prop, PropFalse):
        return prop
    if isinstance(prop, PropImplies):
        return Implies(to_z3(prop.left), to_z3(prop.right))
    if isinstance(prop, PropOr):
        return Or(to_z3(prop.left), to_z3(prop.right))
    if isinstance(prop, PropAnd):
        return And(to_z3(prop.left), to_z3(prop.right))
    if isinstance(prop, PropNot):
        return Not(to_z3(prop.p))


#####################
# please implement the nnf(), cnf() and dpll() algorithm, as discussed
# in the class.
def nnf(prop: Prop) -> Prop:
    if isinstance(prop, PropVar):
        return Bool(prop.var)
    if isinstance(prop, PropTrue):
        return prop
    if isinstance(prop, PropFalse):
        return prop
    if isinstance(prop, PropImplies):
        return PropOr(PropNot(nnf(prop.left)), nnf(prop.right))
    if isinstance(prop, PropOr):
        return PropOr(nnf(prop.left), nnf(prop.right))
    if isinstance(prop, PropAnd):
        return PropAnd(nnf(prop.left), nnf(prop.right))
    if isinstance(prop, PropNot):
        if isinstance(prop.p, PropVar):
            return PropNot(prop.p)
        elif isinstance(prop.p, PropNot):
            return nnf(prop.p.p)
        elif isinstance(prop.p, PropOr):
            return PropAnd(nnf(PropNot(prop.p.left)), nnf(PropNot(prop.p.right)))
        elif isinstance(prop.p, PropAnd):
            return PropOr(nnf(PropNot(prop.p.left)), nnf(PropNot(prop.p.right)))




def is_atom(nnf_prop: Prop) -> bool:
    if isinstance(nnf_prop, PropOr) or isinstance(nnf_prop, PropAnd):
        return False
    return True



def cnf(nnf_prop: Prop) -> Prop:
    def cnf_d(left: Prop, right: Prop) -> Prop:
        if isinstance(left, PropAnd):
            if isinstance(right, PropAnd):
                return PropAnd(PropAnd(cnf_d(left.left, right.left),cnf_d(left.left, right.right)), \
                       PropAnd(cnf_d(left.right, right.left),cnf_d(left.right, right.right)))
            else:
                return PropAnd(cnf_d(left.left, right), cnf_d(left.right, right))

        else:
            if isinstance(right, PropAnd):
                return PropAnd(cnf_d(left, right.left), cnf_d(left, right.right))
            else:
                return PropOr(left, right)




    if isinstance(nnf_prop, PropVar):
        return Bool(nnf_prop.var)
    if isinstance(nnf_prop, PropAnd):
        return PropAnd(cnf(nnf_prop.left), cnf(nnf_prop.right))
    if isinstance(nnf_prop, PropNot):
        return PropNot(cnf(nnf_prop.p))
    if isinstance(nnf_prop, PropOr):
        return cnf_d(cnf(nnf_prop.left), cnf(nnf_prop.right))
    else:
        return nnf_prop





    # raise ("Exercise 3-3: try to implement the `cnf`and `cnf_d` method")


def flatten(cnf_prop: Prop) -> List[List[Prop]]:
    """Flatten CNF Propositions to nested list structure .

    The CNF Propositions generated by `cnf` method is AST.
    This method can flatten the AST to a nested list of Props.
    For example: "((~p1 \\/ ~p3) /\\ (~p1 \\/ p4))" can be
    transfer to "[[~p1, ~p3], [~p1, p4]]".

    Parameters
    ----------
    cnf_prop : Prop
        CNF Propositions generated by `cnf` method.

    Returns
    -------
    List[List[Prop]
        A nested list of Props, first level lists are connected by `And`,
        and second level lists is connected by `Or`.

    """

    def get_atom_from_disjunction(prop: Prop) -> List[Prop]:
        if is_atom(prop):
            return [prop]

        if isinstance(prop, PropOr):
            return get_atom_from_disjunction(prop.left) + get_atom_from_disjunction(prop.right)

    if isinstance(cnf_prop, PropAnd):
        return flatten(cnf_prop.left) + flatten(cnf_prop.right)
    elif isinstance(cnf_prop, PropOr):
        return [get_atom_from_disjunction(cnf_prop)]
    elif is_atom(cnf_prop):
        return [[cnf_prop]]
def dpll(prop: Prop) -> dict:
    flatten_cnf = flatten(cnf(nnf(prop)))
    solution = []
    # print(flatten_cnf)

    def DeepCopy(S):  # 深拷贝
        return copy.deepcopy(S)

    def Simplify(S, p):
        if isinstance(p, PropVar):
            p_name = p.__repr__()
            np_name = '~' + p.__repr__()
        else:
            p_name = p.__repr__()[1:]
            np_name = p.__repr__()
        for disconjuction in S:
            for prop in disconjuction:
                print(prop)
                if prop.__repr__() == p_name or prop.__repr__() == np_name:
                    disconjuction.remove(prop)
            if len(disconjuction) == 0:
                S.remove(disconjuction)
            print(S)
        return S

    def UnitP(S):
        for item in S:
            if item.__len__() == 1:
                return True, item[0]
        return False, None

    def NotConflict(S, p):
        if isinstance(prop, PropVar):
            p_name = prop.__repr__()
            np_name = '~' + prop.__repr__()
        else:
            p_name = prop.__repr__()[1:]
            np_name = prop.__repr__()
        has_p = False
        has_np = False
        for i in range(len(S)):
            if len(S[i]) == 1:
                if S[i][0].__repr__() == p_name:
                    has_p = True
                elif S[i][0].__repr__() == np_name:
                    has_np = True
        if has_p and has_np:
            return False
        else:
            return True
    def transfer_dict(solution: []) -> dict:
        solution_dict = {}
        for prop in solution:
            if isinstance(prop, PropVar):
                prop_name = prop.__repr__()
                solution_dict[prop_name] = True
            else:
                prop_name = prop.__repr__()[1:]
                solution_dict[prop_name] = False

        return solution_dict

    def dpllCore(S: [[Prop]]):

        # 递归出口
        if S.__len__() == 0:
            return True
        IsReP, p = UnitP(S)

        # 判断是否冲突
        while IsReP:
            if NotConflict(S, p):
                solution.append(p)
                S = Simplify(S, p)
            else:
                return False
            IsReP, p = UnitP(S)

        # 再次判断S的大小
        if S.__len__() == 0:
            return True

        single = S[0][0]
        # print(single)
        # 假设可以
        L = solution.__len__()
        solution.append(single)

        # 深拷贝
        temp_S = DeepCopy(S)
        # 递归
        if dpllCore(Simplify(temp_S, single)):
            return True
        else:
            del solution[L:]
            if isinstance(single, PropVar):
                temp_prop = PropNot(single.__repr__())
            else:
                temp_prop = PropVar(single.__repr__()[1:])
            solution.append(temp_prop)
            temp_S = DeepCopy(S)
            return dpllCore(Simplify(temp_S, temp_prop))

    is_sat = dpllCore(flatten_cnf)
    # print(solution)
    if is_sat:
        solution_dict = transfer_dict(solution)
    else:
        return unsat

    return solution_dict



#####################
# test cases:

# p -> (q -> p)
test_prop_1 = PropImplies(PropVar('p'), PropImplies(PropVar('q'), PropVar('p')))

test_prop_2 = PropNot(PropAnd(
    PropOr(PropVar("p1"), PropNot(PropVar("p2"))),
    PropOr(PropVar("p3"), PropNot(PropVar("p4")))
))


# #####################
class TestDpll(unittest.TestCase):

    def test_to_z3_1(self):
        self.assertEqual(str(to_z3(test_prop_1)), "Implies(p, Implies(q, p))")

    def test_to_z3_2(self):
        self.assertEqual(str(to_z3(test_prop_2)), "Not(And(Or(p1, Not(p2)), Or(p3, Not(p4))))")

    def test_nnf_1(self):
        self.assertEqual(str(nnf(test_prop_1)), "(~p \\/ (~q \\/ p))")


    def test_nnf_2(self):
        self.assertEqual(str(nnf(test_prop_2)), "((~p1 /\\ p2) \\/ (~p3 /\\ p4))")

    def test_cnf_1(self):
        self.assertEqual(str(cnf(nnf(test_prop_1))), "(~p \\/ (~q \\/ p))")
        print(str(cnf(nnf(test_prop_1))))

    def test_cnf_2(self):
        print(str(cnf(nnf(test_prop_2))))
        self.assertEqual(str(cnf(nnf(test_prop_2))),
                         "(((~p1 \\/ ~p3) /\\ (~p1 \\/ p4)) /\\ ((p2 \\/ ~p3) /\\ (p2 \\/ p4)))")

    def test_cnf_flatten_1(self):
        self.assertEqual(str(flatten(cnf(nnf(test_prop_1)))), "[[~p, ~q, p]]")

    def test_cnf_flatten_2(self):
        self.assertEqual(str(flatten(cnf(nnf(test_prop_2)))),
                         "[[~p1, ~p3], [~p1, p4], [p2, ~p3], [p2, p4]]")

    def test_dpll_1(self):
        s = Solver()
        res = dpll(test_prop_1)
        s.add(Not(Implies(res["p"], Implies(res["q"], res["p"]))))
        self.assertEqual(str(s.check()), "unsat")

    def test_dpll_2(self):
        s = Solver()
        res = dpll(test_prop_2)
        s.add(Not(Not(And(Or(res["p1"], Not(res["p2"])), Or(res["p3"], Not(res["p4"]))))))
        self.assertEqual(str(s.check()), "unsat")


if __name__ == '__main__':
    unittest.main()