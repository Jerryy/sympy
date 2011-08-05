"""Matrix-FGLM using sdps. """

from sympy import *
from sympy.polys.groebnertools import *
from sympy.polys.monomialtools import *
from sympy.polys.polytools import *

def incr_k(m, k):
    return tuple(list(m[:k]) + [m[k] + 1] + list(m[k + 1:]))

def decr_k(m, k):
    return tuple(list(m[:k]) + [m[k] - 1] + list(m[k + 1:]))


def basis(G, u, O, K):
    """
    Computes a list of monomials which are not divisible by the leading
    monomials wrt to ``O`` of ``G``. These monomials are a basis of
    `K[X_1, ..., X_n]/(G)`.
    """

    leading_monomials = [sdp_LM(g, u) for g in G]
    candidates = [sdp_one(u, K)[0][0]]
    basis = []

    while candidates:
        t = candidates.pop()
        basis.append(t)

        new_candidates = [incr_k(t, k) for k in xrange(u + 1) if all([monomial_div(incr_k(t, k), lmg) is None for lmg in leading_monomials])]
        candidates.extend(new_candidates)
        candidates.sort(key=lambda m: O(m), reverse=True)  # reverse so pop() gives the smallest monomial

    # remove duplicates
    basis = set(basis)
    basis = list(basis)

    return sorted(basis, key=lambda m: O(m))


def representing_matrix(m, basis, G, u, O, K):
    M = zeros((len(basis), len(basis)))

    for i, v in enumerate(basis):
        r = sdp_rem([(monomial_mul(m, v), K.one)], G, u, O, K)

        for term in r:
            j = basis.index(term[0])  # has to exist because G is Groebner basis and sdp_rem computes full reduction
            M[j, i] = term[1]

    return M

def representing_matrices(basis, G, u, O, K):
    def var(i):
        return tuple([0] * i + [1] + [0] * (u - i))

    return [representing_matrix(var(i), basis, G, u, O, K) for i in xrange(u + 1)]

"""
def representing_matrices2(basis, G, u, O, K):
    def elementary_vector(k):
        r = zeros((len(basis), 1))
        r[k] = 1
        return r

    leading_monomials = [sdp_LM(g, u) for g in G]
    N = dict()
    M = [zeros((len(basis), len(basis))) for _ in xrange(u + 1)]

    for i in xrange(len(basis)):
        N[basis[i]] = elementary_vector(i)

        for k in xrange(u + 1):
            if decr_k(basis[i], k) in basis:
                j = basis.index(decr_k(basis[i], k))
                M[k][i, j] = K.one

    F = [incr_k(m, k) for m in basis for k in xrange(u + 1) if incr_k(m, k) not in basis]
    F = sorted(list(set(F)), key=lambda m: O(m))


    for t in F:
        # t is a strict multiple of a leading monomial of G:
        if t not in leading_monomials:
            for j in xrange(u + 1):
                if decr_k(t, j) in N.keys():  # always exists because I iterate over a sorted F
                    mu = N[decr_k(t, j)]

                    N[t] = zeros((len(basis), 1))
                    for i in xrange(len(mu)):
                        N[t] += mu[i] * M[j][:, i]

                    # MISTAKE: I have to do this for all monomials in N[t], not just t
                    # nah, that's wrong again... see original FGLM paper...
                    for k in xrange(u + 1):
                        if decr_k(t, k) in basis:
                            l = basis.index(decr_k(t, k))  # I suppose j==l in the lecture notes?

                            for i in xrange(u + 1):
                                if N[t][i] != 0:
                                    M[k][i, l] = N[t][i]
                    #break  this gives a few more correct matrix entries...
        else:
            g = filter(lambda f: sdp_LM(f, u) == t, G)[0]
            g = sdp_neg(sdp_del_LT(g), u, O, K)

            N[t] = zeros((len(basis), 1))
            for (m, c) in g:
                N[t] += (c * elementary_vector(basis.index(m)))


            for k in xrange(u + 1):
                if decr_k(t, k) in basis:
                    j = basis.index(decr_k(t, k))

                    for i in xrange(u + 1):
                        if N[t][i] != 0:
                            M[k][i, j] = N[t][i]

    return M
"""
"""
def matphi(G, u, O, K):
    leading_monomials = [sdp_LM(g, u) for g in G]

    N = dict()
    Phi = dict()

    monom = (0,) + (u + 1)
    ListOfNexts = []

    while monom:
        # First case: monom is a leading monomial of a g in G
        if any([monom == lmg for lmg in leading_monomials]):
            N[monom] = sum([-c * elementary_vector()])

            # FUCK
"""



def update(s, v, _lambda, P, deg):
#def update(s, v, P, deg):
    """
    k = min([j for j in xrange(1, len(_lambda) + 1) if j > s and _lambda[j - 1] != 0])  # j >= s?

    for j in xrange(1, deg + 1):
        # In Faugere's lecture notes it said "/ P[k - 1, k - 1]". Days I've wasted! But it's still not correct...
        alpha = P[j - 1, k - 1] / _lambda[k - 1]

        P[j - 1, k - 1], P[s, j - 1] = P[s, j - 1], alpha  # s + 1 -> s?

        if alpha != 0:
            for i in xrange(1, deg + 1):
                if i != s + 1:  # s + 1 -> s?
                    P[i - 1, j - 1] -= alpha * _lambda[i - 1]
    """
    #print("s = ", s)
    k = min([j for j in xrange(s, deg) if _lambda[j] != 0])
    #print("v[k] = ", v[k])

    for j in xrange(deg):
        # This means that
        #
        # row:  (... x ...) * v = 0, so alpha should be -P[j, k] / _lambda[k]
        # wrong...
        #alpha = P[j, k] / _lambda[k]
        alpha = P[k, j] / _lambda[k]

        # for Faugere's example, this works with (s,j)->(j,s). Hmm
        #P[j, k] = P[s, j]
        #P[k, j] = P[j, s]  # s, j -> j, s made [x**3+x+1, y**2+1, z - (x**2 + y)] (grevlex->lex) correct
        #P[s, j] = alpha
        #P[k, j] = P[j, s]
        P[k, j] = P[j, s]
        P[s, j] = alpha


        if alpha != 0:
            for i in xrange(deg):
                if i != s:
                    #print("---")
                    #print(P[i,j])
                    P[i, j] -= alpha * _lambda[i]
                    #print(P[i,j])
                    #print("---")
    #print("P*v_s = ", (P*v)[s])
    return P

def matrix_fglm(polys, u, O_from, O_to, K):
    _basis = basis(polys, u, O_from, K)
    print("len(basis) = ", len(_basis))
    M = representing_matrices(_basis, polys, u, O_from, K)
    #print("representing matrices")
    #M2 = representing_matrices2(_basis, polys, u, O_from, K)
    #print("M:")
    #print(M)
    #print("M2:")
    #print(M2)
    #print("---")

    S = [sdp_one(u, K)[0][0]]  # just the monomial
    w0 = zeros((len(_basis), 1))
    w0[0] = K.one
    V = [w0]
    G = []

    # I think t should not necessarily be (n, 1) but rather the smallest element in L
    #L = [(i, 1) for i in xrange(u + 1)]
    #t = L.pop()
    L = [(i, 0) for i in xrange(u + 1)]
    L.sort(key=lambda (k, l): O_to(incr_k(S[l], k)), reverse=True)
    #print(L)
    t = L.pop()
    #print(t)

    #t = (0, 0)
    #L = [(1, 0)]

    P = eye(len(_basis))

    while True:
        #print("V:")
        #print(V)
        print(len(L), len(G))
        s = len(S)
        #print("s = ", s)
        #print(t)
        v = M[t[0]] * V[t[1]]

        # test:
        #print(incr_k(S[t[1]], t[0]))
        #vpoly = sdp_strip(reversed([(_basis[i], v[i]) for i in xrange(len(_basis))]))  # basis is sorted ascendingly
        #print(vpoly)
        #tv = [(incr_k(S[t[1]], t[0]), K.one)]
        #tv = sdp_rem(tv, polys, u, O_from, K)
        #print(tv)
        # ^ so this gives the same result, then it must be update and P!

        _lambda = P * v

        # i think this is correct (s):
        if all([_lambda[i] == 0 for i in xrange(s, len(_basis))]):  # s+1 will return the original system
            sub = [(S[i], _lambda[i]) for i in xrange(s)]
            sub = sdp_strip(sdp_sort(sub, O_to))  # no dupplicates because S contains no duplicates
            lt = [(incr_k(S[t[1]], t[0]), K.one)]
            G.append(sdp_monic(sdp_sub(lt, sub, u, O_to, K), K))
        else:
            #print("old P*v")
            #print(_lambda)
            P = update(s, v, _lambda, P, len(_basis))
            S.append(incr_k(S[t[1]], t[0]))
            V.append(v)

            def has_single_one(vec):
                n = 0
                for coord in vec:
                    if coord != 0:
                        n += 1
                return n == 1
            # test:
            for vp in V:
                lp = P * v
                if not has_single_one(lp):
                    print("still not correct", v == V[-1]) # seems the new v gives too many nonzero entries!

            #print([P*vp for vp in V])

            L.extend([(i, s) for i in xrange(u + 1)])

            # remove duplicates
            L = list(set(L))
            L.sort(key=lambda (k, l): O_to(incr_k(S[l], k)), reverse=True)

        # remove multiples of leading terms of G:
        # do this outside the else block to avoid unnecessary calculations (sorting may be unnecessary, though)
        # if done inside the else, the resulting GB will not be reduced in general.
        L = [(k, l) for (k, l) in L if all([monomial_div(incr_k(S[l], k), sdp_LM(g, u)) is None for g in G])]


        if L == []:
            return sorted(G, key=lambda g: O_to(sdp_LM(g, u)), reverse=True)

        t = L.pop()

def reduced_gb(G, order, gens, domain):
    H = []

    while G:
        f0 = G.pop()

        if not any([monomial_div(f0.LM(order), f.LM(order)) is not None for f in G + H]):
            H.append(f0)

    R = []

    for i, g in enumerate(H):
        g = reduced(g.as_expr(), H[:i] + H[i + 1:], *gens, order=order, domain=domain, polys=True)[1]
        if not g.is_zero:
            R.append(g)

    return R

def fglm(G, *gens, **args):
    options.allowed_flags(args, ['polys'])

    try:
        polys, opt = parallel_poly_from_expr(G, *gens, **args)
    except PolificationFailed, exc:
        raise ComputationFailed('fglm', len(G), exc)

    domain = opt.domain

    if domain.has_assoc_Field:
        opt.domain = domain.get_field()
    else:
        raise DomainError("can't convert Groebner basis over %s" % domain)

    for i, poly in enumerate(polys):
        poly = poly.set_domain(opt.domain).rep.to_dict()
        polys[i] = sdp_from_dict(poly, opt.order)

    level = len(flatten(gens)) - 1

    G = matrix_fglm(polys, level, opt.order, monomial_key('lex'), opt.domain)
    opt.order = monomial_key('lex')
    G = [Poly._from_dict(dict(g), opt).primitive()[1] for g in G]

    # do reduction here because using matrices mixes core rationals with mpqs,
    # which causes sdp_rem to give an error:
    #G = reduced_gb(G, 'lex', gens, opt.domain)

    if not domain.has_Field:
        G = [g.clear_denoms(convert=True)[1] for g in G]

    if not opt.polys:
        return [g.as_expr() for g in G]
    else:
        return G

