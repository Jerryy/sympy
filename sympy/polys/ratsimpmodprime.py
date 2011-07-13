from groebnertools import *
from sympy import symbols, solve, monomials, flatten
from polytools import *

def _normalform(f, G, gens, opt, current_domain):
    polys = []

    for poly in [f] + G:
        polys.append(sdp_from_dict(poly.rep.to_dict(), monomial_key(opt.order)))

    print(polys)

    # annoying problem: the coefficients of polys[0] are polynomials in C, D.
    # perhaps it would be better to write a normalform function for Polys instead
    # of using the one for sdps.

    r = sdp_rem(polys[0], polys[1:], len(gens) - 1, monomial_key(opt.order), current_domain)
    r = Poly._from_dict(dict(r), opt)
   
    return r

def staircase(G, n, gens, order):
    M = [Poly(m, gens) for m in monomials(gens, n)]

    indices = []

    for i, m in enumerate(M):
        for g in G:
            if monomial_div(Poly(m, gens).LM(order), g.LM(order)) is not None:
                indices.append(i)
                break
    
    for i in reversed(indices):
        del M[i]

    return M


def _ratsimp_mod_prime(a, b, G, gens, opt, N=0, D=0):
    c, d = a, b
    steps = 0

    domain = a.domain

    while N + D < a.total_degree() + b.total_degree():
        M1 = staircase(G, N, gens, opt.order)
        M2 = staircase(G, D, gens, opt.order)
   

        C = symbols("c:%d" % len(M1))
        D = symbols("d:%d" % len(M2))

        c_hat = sum([Poly(C[i], gens) * M1[i] for i in xrange(len(M1))])
        d_hat = sum([Poly(D[i], gens) * M2[i] for i in xrange(len(M2))])

        current_domain = domain[C + D]

        r = _normalform(a * d_hat - b * c_hat, G, gens, opt, current_domain)

        S = r.coeffs()

        sol = solve(S, C + D)

        if sol is not None:
            c = c_hat.subs(sol)
            d = d_hat.subs(sol)
            break

        N += 1
        D += 1
        steps += 1

    if steps > 0:
        c, d = ratsimp_mod_prime(c, d, G, order, N, D - steps)
        c, d = ratsimp_mod_prime(c, d, G, order, N - steps, D)

    return c, d

def ratsimp_mod_prime_ideal(a, b, G, *gens, **args):
    options.allowed_flags(args, ['polys'])
    
    try:
        polys, opt = parallel_poly_from_expr([a, b] + G, *gens, **args)
    except PolificationFailed, exc:
        raise ComputationFailed("ratsimp_mod_prime_ideal", len(G), exc)

    #domain = opt.domain

    #if domain.has_assoc_Field:
    #    opt.domain = domain.get_field()
    #else:
    #    raise DomainError("can't compute simplification over %s" % domain)

    gens = flatten(gens)

    c, d = _ratsimp_mod_prime(polys[0], polys[1], polys[2:], gens, opt)

    if domain.has_Field:
        [c, d] = [g.clear_denoms(convert=True)[1] for g in [c, d]]
    if not opt.polys:
        return c.as_expr(), d.as_expr()
    else:
        return c, d
