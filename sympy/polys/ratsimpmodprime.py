from groebnertools import *
from sympy import symbols, solve, monomials, flatten
from polytools import *
from sympy import expand

def normalform_expr(f, G, order):
    r = 0
    while f:
        for g in G:
            ltf = f.as_ordered_terms(order)[0]
            ltg = g.as_ordered_terms(order)[0]

            if (ltf / ltg).is_polynomial():
                f = expand(f - (ltf / ltg) * g)
                break
        else:
            r = r + f.as_ordered_terms(order)[0]
            f = f - f.as_ordered_terms(order)[0]
    return r

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
   

        Cs = symbols("c:%d" % len(M1))
        Ds = symbols("d:%d" % len(M2))

        c_hat = sum([Cs[i] * M1[i] for i in xrange(len(M1))])
        d_hat = sum([Ds[i] * M2[i] for i in xrange(len(M2))])

        r = normalform_expr(expand(a * d_hat - b * c_hat), G, order)

        S = Poly(r, gens).coeffs()
        print(S)

        sol = solve(S, Cs + Ds)

        if sol is not None and not all([s == 0 for s in sol.itervalues()]):
            c = c_hat.subs(sol)
            d = d_hat.subs(sol)
            break

        N += 1
        D += 1
        steps += 1

    if steps > 0:
        print(c, d)
        c, d = ratsimp_mod_prime(c, d, G, order, N, D - steps)
        c, d = ratsimp_mod_prime(c, d, G, order, N - steps, D)

    return c, d
