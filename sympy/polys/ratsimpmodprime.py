from groebnertools import *
from sympy import symbols, solve, monomials, flatten
from polytools import *
from sympy import expand

def normalform(f, G, order, gens):
    """
    Computes the complete reduction of ``f`` modulo ``G``
    w.r.t. ``order``.
    """
    def term((m, c)):
        r = 1 
        for i, v in enumerate(gens):
            r *= v**m[i]
        return c * r

    r = Poly(0, f.gens)
    while not f.is_zero:
        for g in G:
            if monomial_div(f.LM(order), g.LM(order)) is not None:
                ltf = term(f.LT(order))
                ltg = term(g.LT(order))
                f = f - Poly(ltf/ltg, f.gens) * g
                break
        else:
            ltf = f.as_expr().as_ordered_terms(order)[0]
            r = r + Poly(ltf, f.gens)
            f = f - Poly(ltf, f.gens)
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
    print("ratsimp called")
    c, d = a, b
    steps = 0

    #domain = a.domain

    while N + D < a.total_degree() + b.total_degree():
        M1 = staircase(G, N, gens, order)
        M2 = staircase(G, D, gens, order)
   

        Cs = symbols("c:%d" % len(M1))
        Ds = symbols("d:%d" % len(M2))

        c_hat = Poly(sum([Cs[i] * M1[i] for i in xrange(len(M1))]), gens)
        d_hat = Poly(sum([Ds[i] * M2[i] for i in xrange(len(M2))]), gens)

        #print(a * d_hat - b * c_hat)
        #print(type(a * d_hat - b * c_hat))

        r = normalform(a * d_hat - b * c_hat, G, order, gens)

        S = r.coeffs()

        sol = solve(S, Cs + Ds)

        # remove solution of the form ``d2: -d3``
        for key in sol.keys():
            sol[key] = sol[key].subs(dict(zip(Cs + Ds, [0] * (len(Cs) + len(Ds)))))

        if sol is not None and not all([s == 0 for s in sol.itervalues()]):
            c = c_hat.subs(sol)
            d = d_hat.subs(sol)

            # remove remaining variables (if the system was overdetermined)
            c = Poly(c.subs(dict(zip(Cs + Ds, [0] * (len(Cs) + len(Ds))))), gens)
            d = Poly(d.subs(dict(zip(Cs + Ds, [0] * (len(Cs) + len(Ds))))), gens)
            print("c: ", c, Cs)
            print("d: ", d, Ds)
            break

        print("foo")

        N += 1
        D += 1
        steps += 1

    if steps > 0:
        print(c, d)
        c, d = ratsimp_mod_prime(c, d, G, gens, order, N, D - steps)
        c, d = ratsimp_mod_prime(c, d, G, gens, order, N - steps, D)

    return c, d
