"""
F5+ (although I'm starting with the classical F5)
"""

# a rule is a tuple (t, k), where t is a monomial, k a natural number
# a labeled polynomial is a tuple (p, s, n), where p is a sdp, s a signature and n a non-negative integer

from sympy.polys.groebnertools import *

from sympy.polys.monomialtools import monomial_gcd

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

def lbp(p, s, n, b):
    return (p, s, n, b)

def poly(r):
    return r[0]

def S(r):
    return r[1]

def num(r):
    return r[2]

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

def sig_monomial_mul(s, m):
    return (monomial_mul(s[0], m), s[1])

def add_rule(r, Rules):
    Rules[S(r)[1]].insert(0, (S(r)[0], num(r)))


def rewritten(u, r, Rules):
    L = Rules[S(r)[1]]

    ut = monomial_mul(u[0], S(r)[0])

    for l in L:
        if monomial_div(ut, l[0]) is not None:
            return l[1]

    return num(r)

def is_rewritten(u, r, Rules):
    l = rewritten(u, r, Rules)
    return l != num(r)
        

def faugere_criterion(u, r, G):
    for g in G:
        if S(g)[1] > S(r)[1]:
            if monomial_div(monomial_mul(S(r)[0], u[0]), sdp_LM(g, u)) is not None:
                return True
    return False

def rewritten_criterion(u, r, G):
    for g in G:
        if S(g)[1] == S(r)[1]:
            num(g) > num(r):
                if monomial_div(monomial_mul(S(r)[0], u[0]), S(g)[0]) is not None:
                    return True
    return False

def buchberger_lcm_criterion(f, g, u, O):
    if monomial_gcd(sdp_LM(f, u), sdp_LM(g, u)) == (0,) * (u + 1):
        return True
    return False

def incremental_f5(F, u, O, K):
    N = [len(F)]
    Rules = [[] for n in xrange(N[0])]

    r = lbp(F[-1], sig((0,) * (u + 1), N[0] - 1), N[0] - 1, 0)
    G = [r]

    for i in reversed(xrange(len(F) - 1)):
        G = algorithm_f5(i, F[i], G, N, Rules, u, O, K)
        print("is_groebner: ", is_groebner([poly(g) for g in G], u, O, K))
        print(len(G))

    #G = red_groebner([poly(g) for g in G], u, O, K)
    G = [poly(g) for g in G]

    if not is_groebner(G, u, O, K):
        print("Not Groebner basis")

    return sorted(G, key = lambda f: O(sdp_LM(f, u)), reverse = True)

def algorithm_f5(i, f, G, N, Rules, u, O, K):
    ri = lbp(f, sig((0,) * (u + 1), i), i, 0) # number might be wrong
    
    n = len(G)
    NF = lambda g: sdp_rem(g, [poly(r) for r in G[:n]], u, O, K)

    G.append(ri)

    #P = [critical_pair(ri, r, i, NF, u, O, K) for r in G[:n]]
    #P = filter(None, P)

    P = []
    Pstar = []

    for r in G[:-1]:
        p = critical_pair(ri, r, i, NF, u, O, K)
        if p is None and not is_redundant(r):
            Pstar.append((monomial_lcm(sdp_LM(poly(ri), u), sdp_LM(poly(r), u)), ri, r))
        else:
            P.append(p)

    P = filter(None, P)

    print(len(P))
    while P:
        d = min([sum(cp[0]) for cp in P])

        if len(Pstar) == 0:
            max_d = 0 # not sure
        else:
            max_d = max([sum(cp[0]) for cp in Pstar])
        # discard from P* all pairs that are not of maximal degree:
        Pstar = [cp for cp in Pstar if sum(cp[0]) == max_d]

        print(d, max_d)

        if d <= max_d or any([buchberger_criterion(cp, u) == False for cp in Pstar]):
            print("foo")
            Pd = []
            indices = []
            for j, cp in enumerate(P):
                if sum(cp[0]) == d:
                    Pd.append(cp)
                    indices.append(j)
        
            for j in reversed(indices):
                del P[j]

            F = spol(Pd, NF, N, Rules, u, O, K)
            Rd = reduction(F, G, i, NF, N, Rules, u, O, K)

            for r in Rd:
                for g in G:
                    p = critical_pair(r, g, i, NF, u, O, K)
                    if p is None and not is_redundant(r) and not is_redundant(g):
                        Pstar.append((monomial_lcm(sdp_LM(poly(r), u), sdp_LM(poly(g), u)), r, g))
                    else:
                        P.append(p)

                G.append(r)

            P = filter(None, P)
        else:
            P = []

    return G

def critical_pair(r1, r2, k, NF, u, O, K):
    p1, p2 = poly(r1), poly(r2)
    t = (monomial_lcm(sdp_LM(p1, u), sdp_LM(p2, u)), K.one)

    if K.has_Field:
        term_div = _term_ff_div
    else:
        term_div = _term_rr_div

    u1, u2 = term_div(t, sdp_LT(p1, u, K), K), term_div(t, sdp_LT(p2, u, K), K)

    if sig_cmp(sig_monomial_mul(S(r1), u1[0]), sig_monomial_mul(S(r2), u2[0]), O) < 0:
        return critical_pair(r2, r1, k, NF, u, O, K)

    if S(r1)[1] > k:
        return None

    ut1 = [(monomial_mul(u1[0], S(r1)[0]), K.one)]
    if NF(ut1) != ut1:
        return None

    if S(r2)[1] == k:
        ut2 = [(monomial_mul(u2[0], S(r2)[0]), K.one)]
        if NF(ut2) != ut2:
            return None

    return (t[0], u1, r1, u2, r2)

def spol(P, NF, N, Rules, u, O, K):
    F = []

    for l, cp in enumerate(P):
        if not is_rewritten(cp[1], cp[2], Rules):
            if not is_rewritten(cp[3], cp[4], Rules):
                N[0] += 1

                f = sdp_sub(sdp_mul_term(poly(cp[2]), cp[1], u, O, K), sdp_mul_term(poly(cp[4]), cp[3], u, O, K), u, O, K)
                rn = lbp(f, sig_monomial_mul(S(cp[2]), cp[1][0]), N[0], 0) # ?

                add_rule(rn, Rules)

                F.append(rn)

    F.sort(lambda f, g: sig_cmp(S(f), S(g), O))

    return F

def reduction(todo, G, k, NF, N, Rules, u, O, K):
    done = []

    n = len(todo)

    while todo:
        print("todo: ", len(todo))
        todo.sort(lambda f, g: sig_cmp(S(f), S(g), O))
        h = todo.pop()

        h = lbp(NF(poly(h)), S(h), num(h), 0)
        h1, todo1 = top_reduction(h, G + done, k, NF, N, Rules, u, O, K)
        
        done.extend(h1)
        todo.extend(todo1)
   
    return done

def is_reducible(r, G, k, NF, Rules, u, O, K):
    if K.has_Field:
        term_div = _term_ff_div
    else:
        term_div = _term_rr_div

    """
    #print("is_reducible called", len(G))

    #for j, rj in enumerate(G):
    #    t = term_div(sdp_LT(poly(r), u, K), sdp_LT(poly(rj), u, K), K)
    #    if t is not None:
    #        f = sdp_mul_term([t], (S(rj)[0], K.one), u, O, K)
    #        if NF(f) == f:
    #            if not is_rewritten(t, rj, Rules):
    #                if sig_monomial_mul(S(rj), f[0][0]) != S(r):
    #                    #print("is reducible")
    #                    return rj
    
    b = 0
    for 

    return None
    """
    # I *suppose* the error is here, since todo grows seemingly indefinitly in reduction

    b = 0
    for g in G:
        ut = term_div(sdp_LT(poly(r), u, K), sdp_LT(poly(g), u, K), K)
        if ut is not None:
            # ???
            if not faugere_criterion(ut, g, G, u, O, K) and not rewritten_criterion(ut, g, G, u, O, K):
                return g, 0
            else:
                b = 1
    return None, b

def top_reduction(r, G, k, NF, N, Rules, u, O, K):
    if K.has_Field:
        term_div = _term_ff_div
    else:
        term_div = _term_rr_div

    if poly(r) == []:
        return [], []

    rp, b = is_reducible(r, G, k, NF, Rules, u, O, K)

    if rp is None:
        return [lbp(sdp_monic(poly(r), K), S(r), num(r), b)], []
    else:
        rk1 = rp

        ut = term_div(sdp_LT(poly(r), u, K), sdp_LT(poly(rk1), u, K), K)

        if sig_cmp(sig_monomial_mul(S(rk1), ut[0]), S(r), O) < 0:
            r = lbp(sdp_sub(poly(r), sdp_mul_term(poly(rk1), ut, u, O, K), u, O, K), S(r), num(r), b)
            return [], [r]
        else:
            N[0] += 1
            rn = lbp(sdp_sub(sdp_mul_term(poly(rk1), ut, u, O, K), poly(r), u, O, K), sig_monomial_mul(S(rk1), ut[0]), N[0], b)
            add_rule(rn, Rules)
            return [], [rn, r]

def is_groebner(G, u, O, K):
    for i in xrange(len(G)):
        for j in xrange(i + 1, len(G)):
            s = sdp_spoly(G[i], G[j], u, O, K)
            s = sdp_rem(s, G, u, O, K)
            if s != []:
                return False

    return True

def faugere_criterion(ut, r, G, u, O, K):
    for g in G:
        if S(g)[1] > S(r)[1]:
            if monomial_div(monomial_mul(ut[0], S(r)[0]), sdp_LM(poly(g), u)) is not None:
                return True
    return False

def rewritten_criterion(ut, r, G, u, O, K):
    for g in G:
        if S(g)[1] == S(r)[1]:
            if num(g) > num(r):
                if monomial_div(monomial_mul(ut[0], S(r)[0]), sdp_LM(poly(g), u)) is not None:
                    return True
    return False

def buchberger_criterion(cp, G, Pstar, u, O, K):
    for g in G:
        if monomial_div(cp[0], sdp_LM(poly(g), u)) is not None:
            if (monomial_mul(sdp_LM(poly(cp[1]), u), sdp_LM(poly(g), u)), cp[1], g) in Pstar:
                return False
            if (monomial_mul(sdp_LM(poly(g), u), sdp_LM(poly(cp[1]), u)), g, cp[1]) in Pstar:
                return False
            if (monomial_mul(sdp_LM(poly(cp[2]), u), sdp_LM(poly(g), u)), cp[2], g) in Pstar:
                return False
            if (monomial_mul(sdp_LM(poly(g), u), sdp_LM(poly(cp[2]), u)), g, cp[2]) in Pstar:
                return False
    return True

def is_redundant(p):
    return p[3] == 1
