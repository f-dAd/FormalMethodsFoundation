from z3 import *
P, Q, R = Bools('P Q R')
S = Bool('S')
# Exercise 1-1
# (P /\ Q) \/ R
F = Or(And(P, Q), R)
solve(F)
# Exercise 1-5
F = And(F, Not(And(P, Q, Not(R))))
solve(F)

F = And(F, Not(And(P, Q, R)))
solve(F)

F = And(F, Not(And(Not(P), Not(Q), R)))
solve(F)

F = And(F, Not(And(Not(P), Q, R)))
solve(F)

F = And(F, Not(And(P, Not(Q), R)))
solve(F)

# Exercise 1-2
# P \/ (Q \/ R)
F = Or(P, Or(Q, R))
solve(F)

# Exercise 1-3
# (P \/ Q) /\ (Q /\ R) /\ (P /\ ~R)

F = And(And(Or(P, Q), And(Q, R)), And(P, Not(R)))
solve(F)
# Exercise 1-4

# (P /\ ~S /\ R) /\ (R /\ ( ~P \/ (S /\ ~Q)))

F = And(And(P, Not(S), R), And(R, Or(Not(P), And(S, Not(Q)))))
solve(F)