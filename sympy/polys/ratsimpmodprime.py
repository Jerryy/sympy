from groebnertools import *
from sympy import symbols, solve, monomials, flatten
from polytools import *
from sympy import expand

def normalform_expr(f, G, order):
    while True:
        for g in G:
            ltf = f.as_ordered_terms(order)[0]
            ltg = g.as_ordered_terms(order)[0]

            if (ltf / ltg).is_polynomial():
                f = expand(f - (ltf / ltg) * g)
                break
        else:
            break
    return f

def staircase(G, n, gens, order):
    M = list(monomials(gens, n))

    indices = []

    for i, m in enumerate(M):
        for g in G:
            ltg = g.as_ordered_terms(order)[0]
            if (m/ltg).is_polynomial():
                indices.append(i)
                break
    
    for i in reversed(indices):
        del M[i]

    return M


#def _ratsimp_mod_prime(a, b, G, gens, opt, N=0, D=0):
def ratsimp_mod_prime(a, b, G, gens, order, N=0, D=0):
    c, d = a, b
    steps = 0

    #domain = a.domain

    while N + D < Poly(a, gens).total_degree() + Poly(b, gens).total_degree():
        M1 = staircase(G, N, gens, order)
        M2 = staircase(G, D, gens, order)
   

        C = symbols("c:%d" % len(M1))
        D = symbols("d:%d" % len(M2))

        c_hat = sum([C[i] * M1[i] for i in xrange(len(M1))])
        d_hat = sum([D[i] * M2[i] for i in xrange(len(M2))])

        r = normalform_expr(a * d_hat - b * c_hat, G, order)

        S = Poly(r, gens).coeffs()

        sol = solve(S, C + D)

        if sol is not None:
            c = c_hat.subs(sol)
            d = d_hat.subs(sol)
            break

        N += 1
        D += 1
        steps += 1

    if steps > 0:
        c, d = ratsimp_mod_prime(c, d, G, order, N, D - steps)
        c, d = ratsimp_mod_prime(c, d, G, order, N - steps, D)

    return c, d
