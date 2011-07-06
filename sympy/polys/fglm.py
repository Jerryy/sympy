"""
Convert Groebner basis of ideal in two variables from one term order to another
"""
# http://www-salsa.lip6.fr/~jcf/Papers/2010_MPRI5e.pdf

def fglm(G, variables, from_order, to_order):
    L = []
    S = []
    V = []
    G = []
    t = 1  # for now assume QQ

    while True:
        v = normalform(t, G, from_order)
        s = len(S)

        Lambda = symbols("l:%d" % len(V))
        sol = solve(v - sum(Lambda[i] * V[i] for i in xrange(len(V))), Lambda)

        if sol:
            p = t - sum(Lambda[i] * S[i])
            p.subs(sol)
            G.append(p)
        else:
            S.append(t)
            V.append(v)

            L.extend([t * var for var in variables])
            # sort L wrt to_order
            L = set(L)
            L = list(L)
            # remove multiples of LT(G) from L

        if L == []:
            return G

        t = L.pop()
