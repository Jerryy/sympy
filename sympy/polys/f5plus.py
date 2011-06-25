"""
F5+ (although I'm starting with the classical F5)
"""

# a rule is a tuple (t, k), where t is a monomial, k a natural number
# a labeled polynomial is a tuple (p, s, n), where p is a sdp, s a signature and n a non-negative integer

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

def lbp(p, s, n):
    return (p, s, n)

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
    #print("Rules: ", Rules)
    #print(S(r)[1])
    Rules[S(r)[1]].insert(0, (S(r)[0], num(r)))

    #print(Rules)

    # to whoever reads this: I spent HOURS wondering why a rule gets added for *all*
    # indices. The reason was that I had Rules = [[]] * N[0]. Those inner [] are references
    # to the same object (or something like that).

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
        

def incremental_f5(F, u, O, K):
    N = [len(F)]
    Rules = [[] for n in xrange(N[0])]

    r = lbp(F[-1], sig((0,) * (u + 1), N[0] - 1), N[0] - 1)
    #r = lbp(F[0], sig((0,) * (u + 1), 0), 0)
    G = [r]

    for i in reversed(xrange(len(F) - 1)):
    #for i in xrange(1, len(F)):
        #print("current basis %d: " % i, is_groebner([poly(g) for g in G], u, O, K))
        #print("length(basis) == ", len(G))
        G = algorithm_f5(i, F[i], G, N, Rules, u, O, K)
        #print("is_groebner: ", is_groebner([poly(g) for g in G], u, O, K))

    #G = red_groebner([poly(g) for g in G], u, O, K)
    G = [poly(g) for g in G]

    if not is_groebner(G, u, O, K):
        print("Not Groebner basis")

    return sorted(G, key = lambda f: O(sdp_LM(f, u)), reverse = True)

def algorithm_f5(i, f, G, N, Rules, u, O, K):
    ri = lbp(f, sig((0,) * (u + 1), i), i) # number might be wrong
    
    n = len(G)
    NF = lambda g: sdp_rem(g, [poly(r) for r in G[:n]], u, O, K) #lbp(sdp_rem(poly(g), [poly(r) for r in G[:n]], u, O, K), S(g))

    G.append(ri)

    P = [critical_pair(ri, r, i, NF, u, O, K) for r in G[:n]]
    P = filter(None, P)

    #print("P: ", [(num(cp[2]), num(cp[4])) for cp in P])

    while P:
        #print("P: ", [(num(cp[2]), num(cp[4])) for cp in P])
        #print(P, N[0])
        d = min([sum(cp[0]) for cp in P])
        #print("d: ", d)


        Pd = []
        indices = []
        for j, cp in enumerate(P):
            if sum(cp[0]) == d:
                Pd.append(cp)
                indices.append(j)
        
        for j in reversed(indices):
            del P[j]

        F = spol(Pd, NF, N, Rules, u, O, K)
        #print("F: ", [num(f) for f in F])
        Rd = reduction(F, G, i, NF, N, Rules, u, O, K)
        #print("Rd: ", [num(r) for r in Rd])

        for r in Rd:
            for p in G:
                #print("i, algorithm_f5: ", i)
                P.append(critical_pair(r, p, i, NF, u, O, K))

            G.append(r)
            #print("r_%d: " % num(r))
            #print("len(P) == ", len(P))
            

        #P = set(filter(None, P))
        P = filter(None, P)
        #print(len(P))

    #print(G)
    return G

def critical_pair(r1, r2, k, NF, u, O, K):
    #print("critical_pair: ", num(r1), num(r2))
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
        #print("r%d, r%d not cp, S(r1)[1] > %d" % (num(r1), num(r2), k))
        return None

    ut1 = [(monomial_mul(u1[0], S(r1)[0]), K.one)]
    if NF(ut1) != ut1:
        #print("r%d, r%d not cp, ut1 reducible" % (num(r1), num(r2)))
        return None

    if S(r2)[1] == k:
        ut2 = [(monomial_mul(u2[0], S(r2)[0]), K.one)]
        if NF(ut2) != ut2:
            #print("r%d, r%d not cp, S(r2)[1] == %d, and ut2 reducible" % (num(r1), num(r2), k))
            return None

    #print("new critical pair: [r%d, r%d]" % (num(r1), num(r2)))
    return (t[0], u1, r1, u2, r2)

def spol(P, NF, N, Rules, u, O, K):
    F = []

    for l, cp in enumerate(P):
        if not is_rewritten(cp[1], cp[2], Rules):
            if not is_rewritten(cp[3], cp[4], Rules):
                #print("both not rewritten")
                N[0] += 1

                f = sdp_sub(sdp_mul_term(poly(cp[2]), cp[1], u, O, K), sdp_mul_term(poly(cp[4]), cp[3], u, O, K), u, O, K)
                rn = lbp(f, sig_monomial_mul(S(cp[2]), cp[1][0]), N[0])

                add_rule(rn, Rules)

                F.append(rn)

    F.sort(lambda f, g: sig_cmp(S(f), S(g), O))

    #print("spol: ", len(P), len(F))
    return F

def reduction(todo, G, k, NF, N, Rules, u, O, K):
    done = []

    n = len(todo)

    while todo:
        todo.sort(lambda f, g: sig_cmp(S(f), S(g), O))
        h = todo.pop()

        h = lbp(NF(poly(h)), S(h), num(h))
        h1, todo1 = top_reduction(h, G + done, k, NF, N, Rules, u, O, K)
        
        done.extend(h1)
        todo.extend(todo1)
   
    #print("reduction: ", n, len(done)) 
    return done

def is_reducible(r, G, k, NF, Rules, u, O, K):
    if K.has_Field:
        term_div = _term_ff_div
    else:
        term_div = _term_rr_div

    #print("is_reducible called", len(G))

    for j, rj in enumerate(G):
        t = term_div(sdp_LT(poly(r), u, K), sdp_LT(poly(rj), u, K), K)
        if t is not None:
            f = sdp_mul_term([t], (S(rj)[0], K.one), u, O, K)
            if NF(f) == f:
                if not is_rewritten(t, rj, Rules):
                    if sig_monomial_mul(S(rj), f[0][0]) != S(r):
                        #print("is reducible")
                        return rj

    return None

def top_reduction(r, G, k, NF, N, Rules, u, O, K):
    if K.has_Field:
        term_div = _term_ff_div
    else:
        term_div = _term_rr_div

    if poly(r) == []:
        return [], []

    rp = is_reducible(r, G, k, NF, Rules, u, O, K)

    if rp is None:
        return [lbp(sdp_monic(poly(r), K), S(r), num(r))], []
    else:
        rk1 = rp

        ut = term_div(sdp_LT(poly(r), u, K), sdp_LT(poly(rk1), u, K), K)

        if sig_cmp(sig_monomial_mul(S(rk1), ut[0]), S(r), O) < 0:
            r = lbp(sdp_sub(poly(r), sdp_mul_term(poly(rk1), ut, u, O, K), u, O, K), S(r), num(r))
            return [], [r]
        else:
            N[0] += 1
            rn = lbp(sdp_sub(sdp_mul_term(poly(rk1), ut, u, O, K), poly(r), u, O, K), sig_monomial_mul(S(rk1), ut[0]), N[0])
            add_rule(rn, Rules)
            return [], [rn, r]

def red_groebner(G, u, O, K):
    """
    Compute reduced Groebner basis, from BeckerWeispfenning93, p. 216
    """

    def reduction(P, u, O, K):
        """
        Reduction algorithm from BeckerWeispfenning93, p. 203
        """
    
        Q = P
        reducible = True

        while reducible:
            reducible = False
            for i, p in enumerate(Q):
                r = sdp_rem(p, Q[:i] + Q[i + 1:], u, O, K)
                if r != []:
                    del Q[i]
                    Q.append(r)
                    break

        return [sdp_monic(p, K) for p in Q]

    F = G
    H = []

    reducible = False

    while F:
        reducible = True
        f0 = F.pop()

        for f in F + H:
            if monomial_div(sdp_LM(f0, u), sdp_LM(f, u)) is not None:
                reducible = False
                break
        
        if reducible:
            H.append(f0)

    return reduction(H, u, O, K)

def is_groebner(G, u, O, K):
    for i in xrange(len(G)):
        for j in xrange(i + 1, len(G)):
            s = sdp_spoly(G[i], G[j], u, O, K)
            s = sdp_rem(s, G, u, O, K)
            if s != []:
                return False

    return True
