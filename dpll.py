import unittest
from typing import List

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

    # implement the dpll algorithm we've discussed in the lecture
    # you can deal with flattened cnf which generated by `flatten` method for convenience,
    # or, as another choice, you can process the original cnf destructure generated by `cnf` method
    #
    # your implementation should output the result as dict like :
    # {"p1": True, "p2": False, "p3": False, "p4": True} if there is solution;
    # output "unsat" if there is no solution
    #
    # feel free to add new method.
    x = flatten_cnf[0]


    def UnitP(flatten_cnf):
        for item in flatten_cnf:
            if item.__len__() == 1:
                return True, item[0]
        return False, -1

    def NotConflict(flatten_cnf, p):
        listp = []
        listp.append(p)
        listNp = []
        listNp.append(-p)
        if listp in flatten_cnf and listNp in flatten_cnf:
            return False
        return True

    global solution
    # 递归出口
    if flatten_cnf.__len__() == 0:
        return True
    IsReP, p = UnitP(flatten_cnf)
    # 判断是否冲突
    while IsReP:
        if NotConflict(flatten_cnf, p):
            solution.append(p)
            S = Simplify(flatten_cnf, p)
        else:
            return False
        IsReP, p = UnitP(S)
    # 再次判断S的大小
    if S.__len__() == 0:
        return True

    # 选取一个长度最小的逻辑子句,并选一个变量
    single = S[0][0]
    min_clause_size = sys.maxsize
    for items in S:
        if min_clause_size > len(items):
            min_clause_size = len(items)
    single = items[0]  # get the first variable
    L = solution.__len__()
    solution.append(single)

    # 深拷贝
    temp_S = DeepCopy(S)
    # 递归
    if DPLL(Simplify(temp_S, single)):
        return True
    else:
        del solution[L:]
        solution.append(-single)
        temp_S = DeepCopy(S)
        return DPLL(Simplify(temp_S, -single))





    # raise Todo("Exercise 3-4: try to implement the `dpll` algorithm")


#####################
# test cases:

# p -> (q -> p)
test_prop_1 = PropImplies(PropVar('p'), PropImplies(PropVar('q'), PropVar('p')))

test_prop =PropNot(PropVar('q'))
# ~((p1 \/ ~p2) /\ (p3 \/ ~p4))
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

    def test_to_z3(self):
        self.assertEqual(str(cnf(nnf(test_prop))), "(p /\\ q)")

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