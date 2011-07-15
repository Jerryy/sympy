from sympy.polys.groebnertools import *
from sympy.matrices import *
from sympy import flatten
from sympy.polys.monomialtools import monomial_key

def weighted_monomial_key(w, order):
    O = monomial_key(order)
    O_w = lambda alpha: O(tuple([a * b for (a, b) in zip(w, alpha)]))
    return O_w

def matrix_monomial_key(M):
    O = monomial_key('lex')
    O_M = lambda alpha: O(flatten((M * Matrix(alpha)).tolist()))
    return O_M

def dot(a, b):
    return sum([a_ * b_ for (a_, b_) in zip(a, b)])

def next_cone(w_old, w_t, V):
    u_last = 1
    for j in xrange(len(V)):
        if dot(w_t, V[j]) < 0:
            u = dot(w_old, V[j])/(dot(w_old, V[j]) - dot(w_t, V[j]))
        if u < u_last:
            u_last = u
    return u_last

def interreduce(G, u, O, K):
    F = G
    H = []

    while F:
        f0 = F.pop()

        if not any([monomial_div(sdp_LM(f0, u), sdp_LM(f, u)) is not None for f in F + H]):
            H.append(f0)

    R = []

    for i, g in enumerate(H):
        g = sdp_rem(g, H[i:] + H[i + 1:], u, O, K)
        if g != []:
            R.append(g)

    return R


def w_initial_forms(G, w, O_new):
    H = []
    for g in G:
        d_w = max([dot(w, t[0]) for t in g])
        p = filter(lambda t: dot(w, t[0]) == d_w, g)
        p = sdp_sort(p, O_new)
        g = sdp_sort(g, O_new)
        H.append((p, g))
    return H

def _groebner_walk(G, M_s, M_t, w_s, w_t, u, K):
    M_old = M_s
    G_old = G
    w_new = w_s
    M_new = M_t.row_insert(0, Matrix(w_new).transpose())
    done = False

    while not done:
        O_new = matrix_monomial_key(M_new)

        In = w_initial_forms(G_old, w_new, O_new)
        InG = w_buchberger(In, u, O_new, K)
        G_new = [p[1] for p in InG]
        #G_new = lift(InG, G_old, In, M_new, M_old)
        G_new = interreduce(G_new, u, O_new, K)
        u = next_cone(w_new, w_t, V)

        if w_new == w_t:
            done = True
        else:
            M_old = M_new
            G_old = G_new
            w_new = tuple([(1 - u) * wn + u * wt for (wn, wt) in zip(w_new, w_t)])
            # matrix
    return G_new


# buchberger's algorithm that computes the lifted GB as well

def w_spoly(cp, u, O, K):
    if K.has_Field:
        term_div = _term_ff_div
    else:
        term_div = _term_rr_div

    lcm = (monomial_lcm(sdp_LM(cp[0][0], u), sdp_LM(cp[1][0], u)), K.one)
    
    f1 = term_div(lcm, sdp_LT(cp[0][0], u, K), K)
    f2 = term_div(lcm, sdp_LT(cp[1][0], u, K), K)

    sw = sdp_sub(sdp_mul_term(cp[0][0], f1, u, O, K), sdp_mul_term(cp[1][0], f2, u, O, K), u, O, K)
    sg = sdp_sub(sdp_mul_term(cp[0][1], f1, u, O, K), sdp_mul_term(cp[1][1], f2, u, O, K), u, O, K)

    return sw, sg

def w_reduction(sw, sg, P, u, O, K):
    """
    Compute the ordinary reduction of sw by the w-initial-forms in P and perform the same operations
    on sg with the corresponding polynomials in P.
    """
    rw = []
    #rg = []

    if K.has_Field:
        term_div = _term_ff_div
    else:
        term_div = _term_rr_div

    while sw:
        for i, p in enumerate(P):
            tq = term_div(sdp_LT(sw, u, K), sdp_LT(p[0], u, K), K)

            if tq is not None:
                sw = sdp_sub(sw, sdp_mul_term(p[0], tq, u, O, K), u, O, K)
                sg = sdp_sub(sg, sdp_mul_term(p[1], tq, u, O, K), u, O, K)

                break
        else:
            rw = sdp_add_term(rw, sdp_LT(sw, u, K), u, O, K)
            # no need to deal with rg here?
            sw = sdp_del_LT(sw)
    
    return rw, sg

def w_buchberger(P, u, O, K):
    """
    P are pairs of (g_w, g), where g_w is the w-initial-form of g
    """

    # critical pairs where not both w-initial-forms are monomials
    CP = [(P[i], P[j]) for i in xrange(len(P)) for j in xrange(i + 1, len(P)) if len(P[i][0]) * len(P[j][0]) != 1]

    while CP:
        # maybe a better selection strategy is needed
        cp = CP.pop()

        sw, sg = w_spoly(cp, u, O, K)
        rw, rg = w_reduction(sw, sg, P, u, O, K)

        if rw != []:
            P.append((rw, rg))

            CP.extend([(p, (rw, rg)) for p in P if len(p[0]) * len(rw) != 1])

    return P

def groebner_walk(F, to_order, *gens, **args):
    options.allowed_flags(args, ['polys'])

    try:
        polys, opt = parallel_poly_from_expr(F, *gens, **args)
    except PolificationFailed, exc:
        raise ComputationFailed('groebner_walk', len(F), exc)

    domain = opt.domain

    if domain.has_assoc_Field:
        opt.domain = domain.get_field()
    else:
        raise DomainError("can't convert Groebner basis over %s" % domain)

    for i, poly in enumerate(polys):
        poly = poly.set_domain(opt.domain).rep.to_dict()
        polys[i] = sdp_from_dict(poly, opt.order)

    level = len(flatten(gens)) - 1

    G = _groebner_walk(polys, to_order, level, opt.order, opt.domain)
    G = [ Poly._from_dict(dict(g), opt) for g in G ]

    if not domain.has_Field:
        G = [ g.clear_denoms(convert=True)[1] for g in G ]

    if not opt.polys:
        return [ g.as_expr() for g in G ]
    else:
        return G
