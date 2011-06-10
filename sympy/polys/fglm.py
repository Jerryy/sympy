"""
Convert Groebner basis of ideal in two variables from one term order to another
"""
# http://www-salsa.lip6.fr/~jcf/Papers/2010_MPRI5e.pdf

from sympy.polys.groebnertools import (
    sdp_sub,
    O_lex,
    monomial_div,
    sdp_LM,
    sdp_sub,
    sdp_sub_term,
    sdp_rem,
    sdp_strip,
)
from sympy.utilities.iterables import flatten

def row(f, T, K):
    n = len(T)
    r = [K.zero] * n
    
    for tf in f:
        i = T.index(tf[0])
        r[i] = tf[1]


    return r

def solve_system(f, V, s, O, u, K):
    # find linear combination V_0 to V_{s-1} s.t. f = \sum_{i=0}^{s-1} lambda_i V_i OR return 0 if no such linear combination exists
    from sympy.matrices import Matrix

    T = set()
    for v in V:
        for t in v:
            T.add(t[0]) # T.add([(t[0], K.one) for t in v]) 

    B = list(T)

    #f ([t[0] == b for t in f for b in B]):
    #    return 0
    for t in f:
        if not any([t[0] == b for b in B]):
            return 0

    #B = [[(m, K.one)] for m in B]
    B.sort(key = lambda m: O([(m, K.one)]))

    # construct the matrix
    A = Matrix([row(v, B, K) for v in V[:s]])
    b = Matrix(row(f, B, K))

    x = A.LUsolve(b)

    try:
        x = A.LUsolve(b)
        return flatten(x.tolist())
    except ValueError:
        return 0


    

def fglm(F, u, O_old, K, O_new):
    #NF = lambda f: sdp_rem(f, F, u, O_old, K)

    L = [] # next terms
    S = [] # staircase
    V = [] # vectorspace basis
    G = []
    t = [((0,) * (u + 1), K.one)]

    k = 0

    while True:
        v = sdp_rem(t, F, u, O_old, K)
        s = len(S)

        # determine if v lies in the vectorspace spanned by V (i.e. solve linear equation)
        if len(V) > 0:
            l = solve_system(v, V, s, O_old, u, K)
            #print(k)
        else:
            l = 0

        if l != 0:
            print(k, len(G), len(S), len(V))
            new_lc = sdp_strip([(S[i], l[i]) for i in xrange(s)])
            #new = sdp_sub(t, new_lc, u, O_new, K)
            new = sdp_sub_term(new_lc, t[0], u, O_new, K) # wrong sign
            print(new)
            print(new_lc)
            print(l)
            G.append(new)
            #print(G)

        else:
            S.append(t)
            V.append(v)
            for i in xrange(u + 1):
                tp = list(t[0][0])
                tp[i] += 1
                L.append(tuple(tp))
           
            #L = list(set(L)) # remove duplicates
            L = set(L)
            L = list(L)
            L.sort(key = lambda m: O_new([tuple([m, K.one])]))

            # remove elements divisible by a lm of G
            indices = []
            for i, l in enumerate(L):
                for g in G:
                    if monomial_div(sdp_LM(g, O_new), l) is not None:
                        indices.append(i)
                        break
            for i in reversed(indices):
                del L[i]

        if len(L) == 0:
            return sorted(G, key = lambda f: O_new(sdp_LM(f, u)), reverse = True)

        print(len(L))
        t = [(L.pop(), K.one)]
        print(len(L))
        k += 1
                

def convert_to_lex(F, u, O, K):
    return fglm(F, u, O, K, O_lex)
