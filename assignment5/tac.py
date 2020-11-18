import unittest

from z3 import *

from counter import counter


class Todo(Exception):
    def __init__(self, msg):
        self.msg = msg

    def __str__(self):
        return self.msg

    def __repr__(self):
        return self.__str__()


##################################
# The abstract syntax for the Tac (three address code) language:
"""
S ::= x=y | x=y+z | x=y-z | x=y*z | x=y/z
F ::= f(x1, ..., xn){S;* return x;}
"""


# statement
class Stmt:
    def __repr__(self):
        return self.__str__()


class StmtAssignVar(Stmt):
    def __init__(self, x, y):
        self.x = x
        self.y = y

    def __str__(self):
        indent_space = "\t"
        return f"{indent_space}{self.x} = {self.y };\n"

class StmtAssignAdd(Stmt):
    def __init__(self, x, y, z):
        self.x = x
        self.y = y
        self.z = z

    def __str__(self):
        indent_space = "\t"
        return f"{indent_space}{self.x} = {self.y } + {self.z};\n"


class StmtAssignSub(Stmt):
    def __init__(self, x, y, z):
        self.x = x
        self.y = y
        self.z = z

    def __str__(self):
        indent_space = "\t"
        return f"{indent_space}{self.x} = {self.y } - {self.z};\n"

class StmtAssignMul(Stmt):
    def __init__(self, x, y, z):
        self.x = x
        self.y = y
        self.z = z

    def __str__(self):
        indent_space = "\t"
        return f"{indent_space}{self.x} = {self.y } * {self.z};\n"


class StmtAssignDiv(Stmt):
    def __init__(self, x, y, z):
        super().__init__()
        self.x = x
        self.y = y
        self.z = z

    def __str__(self):
        indent_space = "\t"
        return f"{indent_space}{self.x} = {self.y } / {self.z};\n"


# function:
class Function:
    def __init__(self, name, args, stmts, ret):
        self.name = name
        self.args = args
        self.stmts = stmts
        self.ret = ret

    def __str__(self):
        arg_str = ",".join(self.args)

        stmts_str = "".join([str(stmt) for stmt in self.stmts])

        return (f"{self.name}({arg_str}){{\n"
                f"{stmts_str}"
                f"\treturn {self.ret};\n"
                f"}}\n")


###############################################
# SSA conversion:

# take a function 'f', convert it to SSA
def to_ssa_func(func: Function) -> Function:
    # init it by putting every argument into the map
    var_map = {arg: arg for arg in func.args}
    # fresh variable generator
    fresh_var = counter(prefix=f"tac_{func.name}")


    def to_ssa_stmt(stmt):
        new_x = next(fresh_var)
        var_map[stmt.x] = new_x

        new_y = var_map[stmt.y]
        if isinstance(stmt, StmtAssignVar):
            return StmtAssignVar(new_x, new_y)
        else:
            new_z = var_map[stmt.z]

        if isinstance(stmt, StmtAssignAdd):
            return StmtAssignAdd(new_x, new_y, new_z)
        # if isinstance(stmt, StmtAssignSub):
        #     return StmtAssignSub(new_x, new_y, new_z)
        if isinstance(stmt, StmtAssignMul):
            return StmtAssignMul(new_x, new_y, new_z)
        # if isinstance(stmt, StmtAssignDiv):
        #     return StmtAssignDiv(new_x, new_y, new_z)

    # to convert each statement one by one:
    new_stmts = [to_ssa_stmt(stmt) for stmt in func.stmts]

    return Function(func.name, func.args, new_stmts, var_map[func.ret])

###############################################
# Generate Z3 constraints:
def gen_cons_stmt(stmt):
    y = Const(stmt.y, DeclareSort('S'))
    if isinstance(stmt, StmtAssignVar):
        return Const(stmt.x, DeclareSort('S')) == y
    else:
        z = Const(stmt.z, DeclareSort('S'))
    if isinstance(stmt, StmtAssignAdd):
        func_name = "f_add"
    if isinstance(stmt, StmtAssignSub):
        func_name = "f_sub"
    if isinstance(stmt, StmtAssignMul):
        func_name = "f_mul"
    if isinstance(stmt, StmtAssignDiv):
        func_name = "f_div"
    return Const(stmt.x, DeclareSort('S')) == z3.Function(func_name,
                                                            DeclareSort('S'),
                                                            DeclareSort('S'),
                                                            DeclareSort('S')).__call__(y, z)


def gen_cons_func(func):
    return [gen_cons_stmt(stmt) for stmt in func.stmts]


###############################################
# Tests

test_case = Function('f',
                     ['s1', 's2', 't1', 't2'],
                     [StmtAssignAdd('a', 's1', 't1'),
                      StmtAssignAdd('b', 's2', 't2'),
                      StmtAssignMul('c', 'a', 'b'),
                      StmtAssignMul('b', 'c', 's1'),
                      StmtAssignVar('z', 'b')],
                     'z')


# class TestTac(unittest.TestCase):
#     ssa = to_ssa_func(test_case)
#     cons = gen_cons_func(ssa)
#
#     def test_print(self):
#         res = ("f(s1,s2,t1,t2){\n\ta = s1 + t1;\n\tb = s2 + t2;\n\tc = a * b;\n\t"
#                "b = c * s1;\n\tz = b;\n\treturn z;\n}\n")
#
#         # f(s1, s2, t1, t2){
#         #   a = s1 + t1;
#         #   b = s2 + t2;
#         #   c = a * b;
#         #   b = c * s1;
#         #   z = b;
#         #   return z;
#         # }
#         print(test_case)
#         self.assertEqual(str(test_case), res)
#
#     def test_to_ssa(self):
#         res = ("f(s1,s2,t1,t2){\n\t_tac_f_0 = s1 + t1;\n\t_tac_f_1 = s2 + t2;\n\t_tac_f_2 = _tac_f_0 * _tac_f_1;\n\t"
#                "_tac_f_3 = _tac_f_2 * s1;\n\t_tac_f_4 = _tac_f_3;\n\treturn _tac_f_4;\n}\n")
#
#         # f(s1, s2, t1, t2){
#         #   _tac_f_0 = s1 + t1;
#         #   _tac_f_1 = s2 + t2;
#         #   _tac_f_2 = _tac_f_0 * _tac_f_1;
#         #   _tac_f_3 = _tac_f_2 * s1;
#         #   _tac_f_4 = _tac_f_3;
#         #   return _tac_f_4;
#         # }
#
#         # print(self.ssa)
#         self.assertEqual(str(self.ssa), res)
#
#     def test_gen_cons(self):
#         res = ("[_tac_f_0 == f_add(s1, t1),"
#                " _tac_f_1 == f_add(s2, t2),"
#                " _tac_f_2 == f_mul(_tac_f_0, _tac_f_1),"
#                " _tac_f_3 == f_mul(_tac_f_2, s1),"
#                " _tac_f_4 == _tac_f_3]")
#         print(self.cons)
#         self.assertEqual(str(self.cons), res)
#
#
# if __name__ == '__main__':
#     unittest.main()