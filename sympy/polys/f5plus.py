"""
F5+ (although I'm starting with the classical F5)
"""

# a rule is a tuple (t, k), where t is a monomial, k a natural number
# a labeled polynomial is a tuple (p, (t, i)) corresponding to (p, t * F_i). ((t, i) is a signature)

from sympy.polys.groebnertools import *

def _term_rr_div(a, b, K):
    """Division of two terms in over a ring. """
    a_lm, a_lc = a
    b_lm, b_lc = b

    monom = monomial_div(a_lm, b_lm)

    if not (monom is None or a_lc % b_lc):
        return monom, K.quo(a_lc, b_lc)
    else:
        return None

def _term_ff_div(a, b, K):
    """Division of two terms in over a field. """
    a_lm, a_lc = a
    b_lm, b_lc = b

    monom = monomial_div(a_lm, b_lm)

    if monom is not None:
        return monom, K.quo(a_lc, b_lc)
    else:
        return None

def sig(m, k):
    return (m, k)

def lbp(p, s):
    return (p, s)

def poly(l):
    return l[0]

def S(r):
    return r[1]

def sig_cmp(s1, s2, O):
    """
    s1 < s2
    """
    if s1[1] > s2[1]:
        return -1
    if s1[1] == s2[1]:
        if cmp(O(s1[0]), O(s2[0])) < 0:
            return -1
    return 1

def sig_monomial_mult(s, m):
    return (monomial_mul(s[0], m), s[1])

def add_rule(r, k):
    Rules[r[1][1]].append((r[1][0], k))

def rewritten(u, r, k):
    L = Rules[r[1][1]]

    ut = monomial_mul(u, r[1][0])

    for l in L:
        m = monomial_div(ut, l[0])
        if m is not None:
            return (m, G[l[1]]) 
    return (u, r)

def rewritable(u, r, k):
    (v, rl) = rewritten(u, r, k)
    return 

def critical_pair(k, r1, r2, NF, u, O, K):
    #t = monomial_lcm(sdp_LM(poly(r1)), sdp_LM(poly(r2)))

    p1, p2 = poly(r1), poly(r2)

    t = (monomial_lcm(sdp_LM(p1, u), sdp_LM(p2, u)), K.one)

    if K.has_Field:
        term_div = _term_ff_div
    else:
        term_div = _term_rr_div

    u1, u2 = term_div(t, sdp_LT(p1, u, K), K), term_div(t, sdp_LT(p2, u, K), K)

    if sig_cmp(sig_monomial_mult(S(r1), u1[0]), sig_monomial_mult(S(r2), u2[0]), O) < 0:
        return critical_pair(k, r2, r1, NF, u, O, K)

    if S(r1)[1] > k:
        return None

    if NF([(monomial_mul(u1[0], S(r1)[0]), K.one)]) != [(monomial_mul(u1[0], S(r1)[0]), K.one)]:
        return None

    if S(r2)[1] == k:
        if NF([(monomial_mul(u2[0], S(r2)[0]), K.one)]) != [(monomial_mul(u2[0], S(r2)[0]), K.one)]:
            return None

    return (t, u1, r1, u2, r2)

def spol(P, NF, u, O, K):
    F = []

    for l, p in enumerate(P):
        if not rewritable(p[1], p[2], l):
            if not rewritable(p[3], p[4], l):
                N += 1
                f = sdp_sub(sdp_term_mul(poly(p[2]), p[1], u, O, K), sdp_term_mul(poly(p[4]), p[3], u, O, K))
                rn = lbp(f, sig_monomial_mult(S(p[2]), p[1]))
                add_rule(rn)
                F.append(rn)
    F.sort(lambda x, y: sig_cmp(S(x), S(y)))
    return F


def incremental_f5(F, u, O, K):
    global N, Rules, G
    N = len(F)
    Rules = [[]] * N
    G = [lbp(F[-1], sig((0,) * (u + 1), N))]

    for i in reversed(xrange(len(F))):
        G = f5(i, F[i], G, u, O, K)

    ret = [poly(g) for g in G]
    N = 0
    Rules = []
    G = []
    return ret

def f5(i, f, G, u, O, K):
    ri = lbp(f, sig((0,) * (u + 1), i))
   
    n = len(G)
    NF = lambda f: sdp_rem(f, G[:n], u, O, K)

    G.append(ri)

    P = [critical_pair(i, ri, r, NF, u, O, K) for r in G]
    P.sort(key = lambda r: sum(sdp_LM(poly(r))))

    while P:
        d = sum(sdp_LM(poly(P[0])))

        Pd = []
        indices = []
        for i, p in enumerate(P):
            if sum(sdp_LM(poly(p))) == d:
                Pd.append(p)
                indices.append(i)
        for i in reversed(indices):
            del P[i]
        
        F = spol(Pd, u, O, K)
        Rd = reduction(F, G, i, NF, u, O, K)

        for r in Rd:
            P.extend([critical_pair(r, p, i, NF, u, O, K) for p in G])
            G.append(r)

        P.sort(key = lambda r: sum(sdp_LM(poly(r))))

    return G

def reduction(todo, Gi, k, NF, u, O, K):
    done = []

    while F:
        todo.sort(lambda f, g: sig_cmp(S(f), S(g)))
        h = todo.pop()

        h1, todo1 = top_reduction(sdp_rem(h, G, u, O, K), Gi + done, k, NF, u, O, K)

        done.extend(h1)
        todo.extend(todo1)

    return done

def is_reducible(r, G, k, NF, u, O, K):
    if K.has_Field:
        term_div = _term_ff_div
    else:
        term_div = _term_rr_div

    for ri in G:
        u = term_div(sdp_LT(r, K), sdp_LT(ri, K))
        if u is not None:
            f = sdp_mul_term([u], (S(ri)[0], K.one), u, O, K)
            if NF(f) == f:
                if not rewritable(u, ri):
                    if sig_monomial_mul(S(ri), f[0][0]) != S(r):
                        return ri
    return None
    

def top_reduction(r, Gi, k, NF, u, O, K):
    if poly(r) == []:
        # not a regular sequence
        return [], []

    rp = is_reducible(r, Gi, k, NF, u, O, K)

    if rp == []:
        return lbp(sdp_monic(poly(r), K), r[1])
    else:
        r1 = rp

        um = monomial_div(sdp_LM(poly(r)), sdp_LM(poly(r1)))

        if sig_cmp(sig_monomial_mult(S(r1), um), S(r)) < 0:
            return [], [lbp(sdp_sub(poly(r), sdp_mul_term(poly(r1), (um, K.one), u, O, K), u, O, K), S(r))]
        else:
            N += 1
            rn = lbp(sdp_sub(sdp_mul_term(poly(r1), (um, K.one), u, O, K), poly(r), u, O, K), sig_monomial_mult(S(r1), u))
            add_rule(rn, N)

            return [], [rn, r]
        





