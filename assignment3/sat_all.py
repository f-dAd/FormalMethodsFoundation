from z3 import *

# Exercise 1-6
# Now it's your turn, let's wrap all these facility into a nice function:
# Read and understand the code, then complete the lost part.

def sat_all(props, f):
    """Get all solutions of given proposition set props that satisfy f

    Arguments:
        props {BoolRef} -- Proposition list
        f {Boolref} -- logical express that consist of props
    """
    solver = Solver()
    solver.add(f)
    result = []
    while solver.check() == sat:
        m = solver.model()
        result.append(m)
        block = []
        for prop in props:
            prop_is_true = m.eval(prop, model_completion=True)

            if prop_is_true:
                new_prop = prop
            else:
                new_prop = Not(prop)

            block.append(new_prop)
        new_f = And(f, Not(And(block)))
        solver.add(new_f)


        # raise ("Exercise 1-6: try to complete the lost part in the function of `set_all`")

    print("the given proposition: ", f)
    print("the number of solutions: ", len(result))

    def print_model(m):
        print(sorted([(d, m[d]) for d in m], key=lambda x: str(x[0])))

    for m in result:
        print_model(m)


# If you complete the function. Try to use it for below props.
if __name__ == '__main__':
    P, Q, R = Bools('P Q R')
    sat_all([P, Q], Or(P, Q))
    sat_all([P], Implies(P, P))
    sat_all([P, Q, R], Or(P, Q, R))


