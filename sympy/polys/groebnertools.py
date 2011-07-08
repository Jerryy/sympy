"""Groebner bases algorithms. """

from sympy.core.compatibility import minkey, cmp

from sympy.polys.monomialtools import (
    monomial_mul,
    monomial_div,
    monomial_lcm,
    monomial_lex_key as O_lex,
    monomial_grlex_key as O_grlex,
    monomial_grevlex_key as O_grevlex,
)

from sympy.polys.distributedpolys import (
    sdp_LC,
    sdp_LM,
    sdp_LT,
    sdp_mul_term,
    sdp_sub,
    sdp_mul_term,
    sdp_monic,
    sdp_rem,
    sdp_strip,
    _term_ff_div,
    _term_rr_div,
)

from sympy.polys.polyerrors import (
    ExactQuotientFailed, DomainError,
)

from sympy.utilities import any, all
from operator import itemgetter

from sympy.polys.polyconfig import query


def sdp_groebner(f, u, O, K, gens='', verbose=False):
    """
    Wrapper around the (default) improved Buchberger and other
    algorithms for Groebner bases. The choice of algorithm can be
    changed via

    >>>> from sympy.polys.polyconfig import setup
    >>>> setup('GB_METHOD', 'method')

    where 'method' can be 'buchberger' or 'f5b'. If an unknown method
    is provided, the default Buchberger algorithm will be used.

    """
    if query('GB_METHOD') == 'buchberger':
        return buchberger(f, u, O, K, gens, verbose)
    elif query('GB_METHOD') == 'f5b':
        return f5b(f, u, O, K, gens, verbose)
    else:
        return buchberger(f, u, O, K, gens, verbose)

# Buchberger algorithm


def buchberger(f, u, O, K, gens='', verbose=False):
    """
    Computes Groebner basis for a set of polynomials in `K[X]`.

    Given a set of multivariate polynomials `F`, finds another
    set `G`, such that Ideal `F = Ideal G` and `G` is a reduced
    Groebner basis.

    The resulting basis is unique and has monic generators if the
    ground domains is a field. Otherwise the result is non-unique
    but Groebner bases over e.g. integers can be computed (if the
    input polynomials are monic).

    Groebner bases can be used to choose specific generators for a
    polynomial ideal. Because these bases are unique you can check
    for ideal equality by comparing the Groebner bases.  To see if
    one polynomial lies in an ideal, divide by the elements in the
    base and see if the remainder vanishes.

    They can also be used to  solve systems of polynomial equations
    as,  by choosing lexicographic ordering,  you can eliminate one
    variable at a time, provided that the ideal is zero-dimensional
    (finite number of solutions).

    **References**

    1. [Bose03]_
    2. [Giovini91]_
    3. [Ajwa95]_
    4. [Cox97]_

    Algorithm used: an improved version of Buchberger's algorithm
    as presented in T. Becker, V. Weispfenning, Groebner Bases: A
    Computational Approach to Commutative Algebra, Springer, 1993,
    page 232.

    Added optional ``gens`` argument to apply :func:`sdp_str` for
    the purpose of debugging the algorithm.

    """
    if not K.has_Field:
        raise DomainError("can't compute a Groebner basis over %s" % K)

    def select(P):
        # normal selection strategy
        # select the pair with minimum LCM(LM(f), LM(g))
        pr = minkey(P, key=lambda pair: O(monomial_lcm(sdp_LM(f[pair[0]], u), sdp_LM(f[pair[1]], u))))
        return pr

    def normal(g, J):
        h = sdp_rem(g, [ f[j] for j in J ], u, O, K)

        if not h:
            return None
        else:
            h = sdp_monic(h, K)
            h = tuple(h)

            if not h in I:
                I[h] = len(f)
                f.append(h)

            return sdp_LM(h, u), I[h]

    def update(G, B, ih):
        # update G using the set of critical pairs B and h
        # [BW] page 230
        h = f[ih]
        mh = sdp_LM(h, u)

        # filter new pairs (h, g), g in G
        C = G.copy()
        D = set()

        while C:
            # select a pair (h, g) by popping an element from C
            ig = C.pop()
            g = f[ig]
            mg = sdp_LM(g, u)
            LCMhg = monomial_lcm(mh, mg)

            def lcm_divides(ip):
                # LCM(LM(h), LM(p)) divides LCM(LM(h), LM(g))
                m = monomial_lcm(mh, sdp_LM(f[ip], u))
                return monomial_div(LCMhg, m)

            # HT(h) and HT(g) disjoint: mh*mg == LCMhg
            if monomial_mul(mh, mg) == LCMhg or (
                not any(lcm_divides(ipx) for ipx in C) and
                not any(lcm_divides(pr[1]) for pr in D)):
                    D.add((ih, ig))

        E = set()

        while D:
            # select h, g from D (h the same as above)
            ih, ig = D.pop()
            mg = sdp_LM(f[ig], u)
            LCMhg = monomial_lcm(mh, mg)

            if not monomial_mul(mh, mg) == LCMhg:
                E.add((ih, ig))

        # filter old pairs
        B_new = set()

        while B:
            # select g1, g2 from B (-> CP)
            ig1, ig2 = B.pop()
            mg1 = sdp_LM(f[ig1], u)
            mg2 = sdp_LM(f[ig2], u)
            LCM12 = monomial_lcm(mg1, mg2)

            # if HT(h) does not divide lcm(HT(g1), HT(g2))
            if not monomial_div(LCM12, mh) or \
                monomial_lcm(mg1, mh) == LCM12 or \
                monomial_lcm(mg2, mh) == LCM12:
                B_new.add((ig1, ig2))

        B_new |= E

        # filter polynomials
        G_new = set()

        while G:
            ig = G.pop()
            mg = sdp_LM(f[ig], u)

            if not monomial_div(mg, mh):
                G_new.add(ig)

        G_new.add(ih)

        return G_new, B_new
      # end of update ################################

    if not f:
        return []

    # replace f with a reduced list of initial polynomials; see [BW] page 203
    f1 = f[:]

    while True:
        f = f1[:]
        f1 = []

        for i in range(len(f)):
            p = f[i]
            r = sdp_rem(p, f[:i], u, O, K)

            if r:
                f1.append(sdp_monic(r, K))

        if f == f1:
            break

    f = [tuple(p) for p in f]
    I = {}            # ip = I[p]; p = f[ip]
    F = set()         # set of indices of polynomials
    G = set()         # set of indices of intermediate would-be Groebner basis
    CP = set()        # set of pairs of indices of critical pairs

    for i, h in enumerate(f):
        I[h] = i
        F.add(i)

    #####################################
    # algorithm GROEBNERNEWS2 in [BW] page 232
    while F:
        # select p with minimum monomial according to the monomial ordering O
        h = minkey([f[x] for x in F], key=lambda f: O(sdp_LM(f, u)))
        ih = I[h]
        F.remove(ih)
        G, CP = update(G, CP, ih)

    # count the number of critical pairs which reduce to zero
    reductions_to_zero = 0

    while CP:
        ig1, ig2 = select(CP)
        CP.remove((ig1, ig2))

        h = sdp_spoly(f[ig1], f[ig2], u, O, K)
        # ordering divisors is on average more efficient [Cox] page 111
        G1 = sorted(G, key=lambda g: O(sdp_LM(f[g], u)))
        ht = normal(h, G1)

        if ht:
            G, CP = update(G, CP, ht[1])
        else:
            reductions_to_zero += 1

    ######################################
    # now G is a Groebner basis; reduce it
    Gr = set()

    for ig in G:
        ht = normal(f[ig], G - set([ig]))

        if ht:
            Gr.add(ht[1])

    Gr = [list(f[ig]) for ig in Gr]

    # order according to the monomial ordering
    Gr = sorted(Gr, key=lambda f: O(sdp_LM(f, u)), reverse=True)

    if verbose:
        print 'reductions_to_zero = %d' % reductions_to_zero

    return Gr


def sdp_str(f, gens):
    if isinstance(gens, basestring):
        gens = gens.split(',')
    ngens = len(gens)
    z = (0,) * ngens
    s = ''
    for expv, c in f:
        if c > 0:
            s += ' +'
        else:
            s += ' -'
        if c < 0:
            c = -c
        if c != 1:  # and expv != z:
            cnt1 = str(c)
        else:
            cnt1 = ''
        sa = []
        for i in range(ngens):
            exp = expv[i]
            if exp > 1:
                sa.append('%s^%d' % (gens[i], exp))
            if exp == 1:
                sa.append('%s' % gens[i])
        if cnt1:
            sa = [cnt1] + sa
        s += '*'.join(sa)
    return s


def sdp_spoly(p1, p2, u, O, K):
    """
    Compute LCM(LM(p1), LM(p2))/LM(p1)*p1 - LCM(LM(p1), LM(p2))/LM(p2)*p2
    This is the S-poly provided p1 and p2 are monic
    """
    LM1 = sdp_LM(p1, u)
    LM2 = sdp_LM(p2, u)
    LCM12 = monomial_lcm(LM1, LM2)
    m1 = monomial_div(LCM12, LM1)
    m2 = monomial_div(LCM12, LM2)
    s1 = sdp_mul_term(p1, (m1, K.one), u, O, K)
    s2 = sdp_mul_term(p2, (m2, K.one), u, O, K)
    s = sdp_sub(s1, s2, u, O, K)
    return s

# F5B

# convenience accessor functions


def Sign(f):
    return f[0]


def Polyn(f):
    return f[1]


def Num(f):
    return f[2]

# signature functions


def sig(monomial, index):
    return (monomial, index)


def sig_cmp(u, v, O):
    """
    Compare two signatures by extending the term order to K[X]^n.

    (u < v)
    """
    if u[1] > v[1]:
        return -1
    if u[1] == v[1]:
        if u[0] == v[0]:
            return 0
        if cmp(O(u[0]), O(v[0])) < 0:
            return -1
    return 1


def sig_mult(s, m):
    """
    Multiply a signature by a monomial.
    """
    return sig(monomial_mul(s[0], m), s[1])

# labeled polynomial functions


def lbp(signature, polynomial, number):
    return (signature, sdp_strip(polynomial), number)


def lbp_sub(f, g, u, O, K):
    """
    Subtract labeled polynomial g from f.
    """
    if sig_cmp(Sign(f), Sign(g), O) == -1:
        max_poly = g
    else:
        max_poly = f

    ret = sdp_sub(Polyn(f), Polyn(g), u, O, K)

    return lbp(Sign(max_poly), ret, Num(max_poly))


def lbp_mul_term(f, cx, u, O, K):
    """
    Multiply a labeled polynomial with a term.
    """
    return lbp(sig_mult(Sign(f), cx[0]), sdp_mul_term(Polyn(f), cx, u, O, K), Num(f))


def lbp_cmp(f, g, O):
    """
    Compare two labeled polynomials. Attention: This relation is
    not antisymmetric!

    (f < g)
    """
    if sig_cmp(Sign(f), Sign(g), O) == -1:
        return -1
    if Sign(f) == Sign(g):
        if Num(f) > Num(g):
            return -1
        if Num(f) == Num(g):
            return 0
    return 1

# algorithm and helper functions


def critical_pair(f, g, u, O, K):
    """
    Compute the critical pair corresponding to two labeled polynomials.
    """
    ltf = sdp_LT(Polyn(f), u, K)
    ltg = sdp_LT(Polyn(g), u, K)
    lt = (monomial_lcm(ltf[0], ltg[0]), K.one)

    if K.has_Field:
        term_div = _term_ff_div
    else:
        term_div = _term_rr_div

    um = term_div(lt, ltf, K)
    vm = term_div(lt, ltg, K)

    # The full information is not needed (now), so only the product
    # with the leading term is considered:
    fr = lbp_mul_term(lbp(Sign(f), [sdp_LT(Polyn(f), u, K)], Num(f)), um, u, O, K)
    gr = lbp_mul_term(lbp(Sign(g), [sdp_LT(Polyn(g), u, K)], Num(g)), vm, u, O, K)

    # return in proper order, such that the S-polynomial is just
    # u_first * f_first - u_second * f_second:
    if lbp_cmp(fr, gr, O) == -1:
        return (Sign(gr), vm, g, Sign(fr), um, f)
    else:
        return (Sign(fr), um, f, Sign(gr), vm, g)


def cp_cmp(c, d, O):
    """
    Compare two critical pairs c and d.

    (c < d)
    """
    c0 = lbp(c[0], [], Num(c[2]))
    d0 = lbp(d[0], [], Num(d[2]))

    if lbp_cmp(c0, d0, O) == -1:
        return -1
    if lbp_cmp(c0, d0, O) == 0:
        c1 = lbp(c[3], [], Num(c[5]))
        d1 = lbp(d[3], [], Num(d[5]))

        if lbp_cmp(c1, d1, O) == -1:
            return -1
        if lbp_cmp(c1, d1, O) == 0:
            return 0
    return 1


def s_poly(cp, u, O, K):
    """
    Compute the S-polynomial of a critical pair.
    """
    return lbp_sub(lbp_mul_term(cp[2], cp[1], u, O, K), lbp_mul_term(cp[5], cp[4], u, O, K), u, O, K)


def is_rewritable_or_comparable(f, B, u, K):
    """
    Check if a labeled polynomial f is rewritable or comparable by B.
    """
    for h in B:
        # comparable
        if Sign(f)[1] < Sign(h)[1]:
            if monomial_div(Sign(f)[0], sdp_LM(Polyn(h), u)) is not None:
                return True

        # rewritable
        if Sign(f)[1] == Sign(h)[1]:
            if Num(f) < Num(h):
                if monomial_div(Sign(f)[0], Sign(h)[0]) is not None:
                    return True
    return False


def f5_single_reduction(f, B, u, O, K):
    """
    Perform a single F5-reduction of a labeled polynomial f by B.

    Searches for a labeled polynomial g in B, such that g is non-zero,
    the leading term lg of g divides the leading term lf of f and
    the signature of lf/lg * g is less than the signature of f. If
    such a g exists, the function returns f - lf/lg * g.
    """
    if Polyn(f) == []:
        return f

    if K.has_Field:
        term_div = _term_ff_div
    else:
        term_div = _term_rr_div

    for g in B:
        if Polyn(g) != []:
            t = term_div(sdp_LT(Polyn(f), u, K), sdp_LT(Polyn(g), u, K), K)
            if t is not None:
                gp = lbp_mul_term(g, t, u, O, K)
                if sig_cmp(Sign(gp), Sign(f), O) == -1:
                    # The following check need not be done and is in general slower than without.
                    #if not is_rewritable_or_comparable(gp, B, u, K):
                    return lbp_sub(f, gp, u, O, K)
    return f


def f5_reduce(f, B, u, O, K):
    """
    F5-reduce a labeled polynomial f by B.

    Calls f5_single_reduction until the labeled polynomial doesn't
    change anymore, which means that it can't be f5-reduced further.
    """
    if Polyn(f) == []:
        return f

    while True:
        g = f
        f = f5_single_reduction(f, B, u, O, K)
        if g == f:
            return f


def f5b(F, u, O, K, gens='', verbose=False):
    """
    Implementation of the F5B algorithm by Yao Sun and Dingkang
    Wang. The algorithm is is very similar to Buchberger's algorithm,
    except that it checks if polynomials are redundant and discards
    them if they are.

    Optimizations include: Reducing the generators before computing
    a Groebner basis, removing redundant critical pairs when a new 
    polynomial enters the basis and sorting the critical pairs and 
    the current basis.

    Once a Groebner basis has been found, it gets reduced.

    ** References **
    Yao Sun, Dingkang Wang: "A New Proof for the Correctness of F5 (F5-Like) Algorithm",
        http://arxiv.org/abs/1004.0084 (specifically v4)

    Thomas Becker, Volker Weispfenning, Groebner bases and commutative algebra, 1993, p. 203, 216
    """
    if not K.has_Field:
        raise DomainError("can't compute a Groebner basis over %s" % K)

    # reduce polynomials (like in Mario Pernici's implementation) (Becker, Weispfenning, p. 203)
    B = F
    while True:
        F = B
        B = []

        for i in xrange(len(F)):
            p = F[i]
            r = sdp_rem(p, F[:i], u, O, K)

            if r != []:
                B.append(r)

        if F == B:
            break

    # basis
    B = [lbp(sig((0,) * (u + 1), i + 1), F[i], i + 1) for i in xrange(len(F))]

    # critical pairs
    CP = [critical_pair(B[i], B[j], u, O, K) for i in xrange(len(B)) for j in xrange(i + 1, len(B))]

    k = len(B)

    reductions_to_zero = 0

    while len(CP):
        cp = CP.pop()

        # the actual polynomial isn't needed for rewritable and comparable checks:
        uf = lbp(cp[0], [], Num(cp[2]))
        vg = lbp(cp[3], [], Num(cp[5]))

        if is_rewritable_or_comparable(uf, B, u, K):
            continue
        if is_rewritable_or_comparable(vg, B, u, K):
            continue

        s = s_poly(cp, u, O, K)

        p = f5_reduce(s, B, u, O, K)

        p = lbp(Sign(p), Polyn(p), k + 1)

        if Polyn(p) != []:
            # remove old critical pairs, that become redundant when adding p:
            indices = []
            for i, cp in enumerate(CP):
                if is_rewritable_or_comparable(lbp(cp[0], [], Num(cp[2])), [p], u, K):
                    indices.append(i)
                elif is_rewritable_or_comparable(lbp(cp[3], [], Num(cp[5])), [p], u, K):
                    indices.append(i)

            for i in reversed(indices):
                del CP[i]

            # only add new critical pairs that are not made redundant by p:
            for g in B:
                if Polyn(g) != []:
                    cp = critical_pair(p, g, u, O, K)
                    if is_rewritable_or_comparable(lbp(cp[0], [], Num(cp[2])), [p], u, K):
                        continue
                    elif is_rewritable_or_comparable(lbp(cp[3], [], Num(cp[5])), [p], u, K):
                        continue
                    CP.append(cp)

            # sort (other sorting methods/selection strategies were not as successful)
            CP.sort(lambda c, d: cp_cmp(c, d, O), reverse=True)
            B.append(p)
            B.sort(key=lambda f: O(sdp_LM(Polyn(f), u)), reverse=True)

            k += 1

            #print(len(B), len(CP), "%d critical pairs removed" % len(indices))
        else:
            reductions_to_zero += 1

    if verbose:
        print("%d reductions to zero" % reductions_to_zero)

    # reduce Groebner basis:
    H = [sdp_strip(sdp_monic(Polyn(g), K)) for g in B]
    H = red_groebner(H, u, O, K)

    return sorted(H, key=lambda f: O(sdp_LM(f, u)), reverse=True)


def red_groebner(G, u, O, K):
    """
    Compute reduced Groebner basis, from BeckerWeispfenning93, p. 216

    Selects a subset of generators, that already generate the ideal
    and computes a reduced Groebner basis for them.
    """
    def reduction(P, u, O, K):
        """
        The actual reduction algorithm.
        """
        Q = []
        for i, p in enumerate(P):
            h = sdp_rem(p, P[:i] + P[i + 1:], u, O, K)
            if h != []:
                Q.append(h)

        return [sdp_monic(p, K) for p in Q]

    F = G
    H = []

    while F:
        f0 = F.pop()

        if not any([monomial_div(sdp_LM(f0, u), sdp_LM(f, u)) is not None for f in F + H]):
            H.append(f0)

    # By Becker, Weispfenning, p. 217: H is Groebner basis of the ideal generated by G.
    return reduction(H, u, O, K)


def is_groebner(G, u, O, K):
    """
    Check if G is a Groebner basis.
    """
    for i in xrange(len(G)):
        for j in xrange(i + 1, len(G)):
            s = sdp_spoly(G[i], G[j], u, O, K)
            s = sdp_rem(s, G, u, O, K)
            if s != []:
                return False

    return True

def is_minimal(G, u, O, K):
    """
    Checks if G is a minimal Groebner basis.
    """
    G.sort(key=lambda g: O(sdp_LM(g, u)))
    for i, g in enumerate(G):
        if sdp_LC(g, K) != K.one:
            return False
        
        for h in G[:i] + G[i + 1:]:
            if monomial_div(sdp_LM(g, u), sdp_LM(h, u)) is not None:
                return False

    return True

def is_reduced(G, u, O, K):
    """
    Checks if G is a reduced Groebner basis.
    """
    G.sort(key=lambda g: O(sdp_LM(g, u)))
    for i, g in enumerate(G):
        if sdp_LC(g, K) != K.one:
            return False

        for term in g:
            for h in G[:i] + G[i + 1:]:
                if monomial_div(term[0], sdp_LM(h, u)) is not None:
                    return False

    return True

