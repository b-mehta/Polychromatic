from z3 import *
from tqdm import trange
import tqdm
import math
import sys

def make_instance(A, B, C, D, period):
    s = Solver()

    # Declare integer variables and functions
    f = Function('f', IntSort(), IntSort())
    a, b, c, d, q = Ints('a b c d q')

    # Assert the given constraints
    s.add(a == A)
    s.add(b == B)
    s.add(c == C)
    s.add(d == D)

    # Define the 'covers' function as a Z3 expression
    def covers(at, bt, ct, dt, i):
        return Or(f(at % q) == i,
                  f(bt % q) == i,
                  f(ct % q) == i,
                  f(dt % q) == i)

    # Add the quantified assertions
    s.add(f(0) == 0)
    s.add(f(1) == 1)

    t = Int('t')
    s.add(ForAll(t, covers(a + t, b + t, c + t, d + t, 0)))
    s.add(ForAll(t, covers(a + t, b + t, c + t, d + t, 1)))
    s.add(ForAll(t, covers(a + t, b + t, c + t, d + t, 2)))

    s.add(q == period)

    return (s, f)

def solve(A, B, C, D, lo=30, hi=80):
    for period in range(lo, hi):
        (s, f) = make_instance(A, B, C, D, period)

        # Check if the constraints are satisfiable
        if s.check() == sat:
            model = s.model()
            z = ",".join(str(model.eval(f(i)+1)) for i in range(period))
            return(f"{A},{B},{C},{D};{period};{z},\n")
            break
    else:
        print(f"no solution found for {A},{B},{C},{D}")
        sys.exit()

missing = []
output = []

with open("temp-colors.log", "r") as f:
    for i in tqdm.tqdm(f.readlines()):
        [abc, q, z] = i.strip().split(';')
        [_, a, b, c] = (int(j) for j in abc.split(','))
        q = int(q)
        if q > 0:
            z = tuple(int(j) for j in z.split(',')[:-1])
            output.append(i)
        else:
            out = solve(0, a, b, c)
            output.append(out)

with open("full-colors.log", "w") as f3:
    f3.write("".join(output))
