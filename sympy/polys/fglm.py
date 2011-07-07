"""
Convert Groebner basis of ideal in two variables from one term order to another
"""
# http://www-salsa.lip6.fr/~jcf/Papers/2010_MPRI5e.pdf

from groebnertools import *
from sympy import eye, zeros

"""
def fglm(G, from_order, to_order, *gens, **args):
    try:
        polys, opt = parallel_poly_from_expr(G, *gens, **args)
    except PolificationFailed, exc:
        raise ComputationFailed('normalform', len(G) + 1, exc)
    
    if opt.domain.has_assoc_Field:
        opt.domain = opt.domain.get_field()
    else:
        raise DomainError("can't convert basis over %s" % K)
    
    for poly in polys:
        poly = poly.set_domain(opt.domain).as_expr()

    gens = flatten(gens)
    opt.order = from_order

    try:
        O = monomial_key(to_order)
    except ValueError, KeyError:
        pass

    L = []
    S = []
    V = []
    G = []
    t = 1  # for now assume QQ

    while True:
        v = _normalform(t, G, gens, opt)
        s = len(S)

        Lambda = symbols("l:%d" % len(V), real=True) # actually rational
        sol = solve(v - sum(Lambda[i] * V[i] for i in xrange(len(V))), Lambda)

        # PROBLEM: I want solve to solve system over rationals (or arbitrary field). besides it's slow.
        # --> have to create linear system where columns correspond to monomials

        if sol:
            print(sol, v - sum([Lambda[i] * V[i] for i in xrange(len(V))]))
            p = t - sum([Lambda[i] * S[i] for i in xrange(len(S))])
            
            if len(Lambda) == 1:
                p = p.subs(Lambda[0], sol[0])
            else:
                P = p.subs(sol)
            print(p)
            G.append(p)
        else:
            print("foo")
            S.append(t)
            V.append(v)

            L.extend([t * var for var in gens])
            L.sort(key=lambda f: O(Poly(f, gens).LM(to_order)))
            
            # remove elements whose LM is a multiple of a LM of G:
            indices = []
            for i, l in enumerate(L):
                if any([monomial_div(Poly(l, gens).LM(to_order), Poly(g, gens).LM(to_order)) is not None for g in G]):
                    indices.append(i)
            for i in reversed(indices):
                del L[i]

        if L == []:
            return G

        t = L.pop()

def _normalform(f, G, gens, opt):
    polys = []
    
    for poly in [f] + G:
        polys.append(sdp_from_dict(Poly(poly, gens).rep.to_dict(), monomial_key(opt.order)))

    r = sdp_rem(polys[0], polys[1:], len(gens) - 1, monomial_key(opt.order), opt.domain)
    r = Poly._from_dict(dict(r), opt).as_expr()

    return r
"""

def gaussian_solve(A, b, K):
    n = min(len(A), len(A[0]))


def gaussian_elimination(A, b):
    M = A[:, :]
    n = min(M.rows, M.cols)
    P = eye(max(M.rows, M.cols))
    x = zeros((M.cols, 1))

    # walk along the diagonal
    for i in xrange(n):
        if M[i, i] == 0:
            # find pivot:
            for j in xrange(i + 1, M.rows):
                if M[j, i] != 0:
                    M.row_swap(i, j)
                    P.row_swap(i, j)
                    b.row_swap(i, j)

        if M[i, i] != 0:
            # pivot not zero, eliminate below:
            for j in xrange(i + 1, M.rows):
                for k in xrange(i, M.cols):
                    M[j, k] = M[j, k] * M[i, i] - M[j, i] * M[i, k]
                b[j] = b[j] * M[i, i] - M[j, i] * b[i]
                print("foo", b[j], M[j, i]/M[i, i])
        
        # no pivot found: simply continue
    
    M = M[0:n, 0:n]
    #b = P * b later

    # backsubstitution (don't care about zeros yet)
    #for i in reversed(xrange(n)):
    #    print(len(x[i + 1:n]), len(M[i, i + 1:n]))
    #    x[i] = (b[i] - sum([z[0] * z[1] for z in zip(x[i:n], M[i, i:n])])) / M[i, i]
    for i in reversed(xrange(n)):
        x[i] = b[i]
        x[i] -= sum([c[0] * c[1] for c in zip(x[i + 1:n], M[i, i + 1:n])])
        x[i] /= M[i, i]

    print(b)
    print(P)
    return P.transpose() * x

def incr_tuple_at(t, i):
    r = list(t)
    r[i] += 1
    return tuple(r)
"""
def fglm(F, from_order, to_order, u, K):
    L = []
    S = []
    V = []
    G = []
    t = (0,) * (u + 1)

    NF = lambda f: sdp_rem(f, F, u, monomial_key(from_order), K)

    while True:
        v = NF([(t, K.one)])
        s = len(S)

        # matrix
        if :
            p = sdp_sub([(t, K.one)], lc, u, monomial_key(from_order), K)
            p = sdp_sort(p, monomial_key(to_order))
            G.append(p)            
        else:
            S.append(t)
            L.extend([incr_tuple_at(i) for i in xrange(u + 1)])
            L.sort(key=lambda m: monomial_key(to_order)(m))

            # remove multiples of LT(G)
            indices = []
            for i, l in enumerate(L):
                if any([monomial_div(l, sdp_LM(g, u)) is not None for g in G]):
                    indices.append(i)

            for i in reversed(indices):
                del L[i]

        if L == []:
            return G

        t = L.pop()
"""
