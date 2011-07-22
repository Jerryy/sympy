"""Solvers of systems of polynomial equations. """

from sympy.polys import Poly, groebner, roots, polyoptions as options
from sympy.polys.polytools import parallel_poly_from_expr
from sympy.polys.polyerrors import ComputationFailed, PolificationFailed
from sympy.polys.monomialtools import monomial_div, monomial_key
from sympy.matrices import Matrix, zeros
from sympy.utilities import postfixes, flatten
from sympy.simplify import rcollect
from sympy.core import S, Dummy, N
from itertools import product

class SolveFailed(Exception):
    """Raised when solver's conditions weren't met. """

def solve_poly_system(seq, *gens, **args):
    """
    Solve a system of polynomial equations.

    Example
    =======

    >>> from sympy import solve_poly_system
    >>> from sympy.abc import x, y

    >>> solve_poly_system([x*y - 2*y, 2*y**2 - x**2], x, y)
    [(0, 0), (2, -2**(1/2)), (2, 2**(1/2))]

    """
    try:
        polys, opt = parallel_poly_from_expr(seq, *gens, **args)
    except PolificationFailed, exc:
        raise ComputationFailed('solve_poly_system', len(seq), exc)

    if len(polys) == len(opt.gens) == 2:
        f, g = polys

        a, b = f.degree_list()
        c, d = g.degree_list()

        if a <= 2 and b <= 2 and c <= 2 and d <= 2:
            try:
                return solve_biquadratic(f, g, opt)
            except SolveFailed:
                pass

    return solve_generic2(polys, opt)

def solve_biquadratic(f, g, opt):
    """Solve a system of two bivariate quadratic polynomial equations. """
    G = groebner([f, g])

    if len(G) == 1 and G[0].is_ground:
        return None

    if len(G) != 2:
        raise SolveFailed

    p, q = G
    x, y = opt.gens

    p = Poly(p, x, expand=False)
    q = q.ltrim(-1)

    p_roots = [ rcollect(expr, y) for expr in roots(p).keys() ]
    q_roots = roots(q).keys()

    solutions = []

    for q_root in q_roots:
        for p_root in p_roots:
            solution = (p_root.subs(y, q_root), q_root)
            solutions.append(solution)

    return sorted(solutions)

def solve_generic(polys, opt):
    """
    Solve a generic system of polynomial equations.

    Returns all possible solutions over C[x_1, x_2, ..., x_m] of a
    set F = { f_1, f_2, ..., f_n } of polynomial equations,  using
    Groebner basis approach. For now only zero-dimensional systems
    are supported, which means F can have at most a finite number
    of solutions.

    The algorithm works by the fact that, supposing G is the basis
    of F with respect to an elimination order  (here lexicographic
    order is used), G and F generate the same ideal, they have the
    same set of solutions. By the elimination property,  if G is a
    reduced, zero-dimensional Groebner basis, then there exists an
    univariate polynomial in G (in its last variable). This can be
    solved by computing its roots. Substituting all computed roots
    for the last (eliminated) variable in other elements of G, new
    polynomial system is generated. Applying the above procedure
    recursively, a finite number of solutions can be found.

    The ability of finding all solutions by this procedure depends
    on the root finding algorithms. If no solutions were found, it
    means only that roots() failed, but the system is solvable. To
    overcome this difficulty use numerical algorithms instead.

    References
    ==========

    .. [Buchberger01] B. Buchberger, Groebner Bases: A Short
    Introduction for Systems Theorists, In: R. Moreno-Diaz,
    B. Buchberger, J.L. Freire, Proceedings of EUROCAST'01,
    February, 2001

    .. [Cox97] D. Cox, J. Little, D. O'Shea, Ideals, Varieties
    and Algorithms, Springer, Second Edition, 1997, pp. 112

    """
    def is_univariate(f):
        """Returns True if 'f' is univariate in its last variable. """
        for monom in f.monoms():
            if any(m > 0 for m in monom[:-1]):
                return False

        return True

    def subs_root(f, gen, zero):
        """Replace generator with a root so that the result is nice. """
        p = f.as_expr({gen: zero})

        if f.degree(gen) >= 2:
            p = p.expand(deep=False)

        return p

    def solve_reduced_system(system, gens, entry=False):
        """Recursively solves reduced polynomial systems. """
        if len(system) == len(gens) == 1:
            zeros = roots(system[0], gens[-1]).keys()
            return [ (zero,) for zero in zeros ]

        basis = groebner(system, gens, polys=True)

        if len(basis) == 1 and basis[0].is_ground:
            if not entry:
                return []
            else:
                return None

        univariate = filter(is_univariate, basis)

        if len(univariate) == 1:
            f = univariate.pop()
        else:
            raise NotImplementedError("only zero-dimensional systems supported (finite number of solutions)")

        gens = f.gens
        gen = gens[-1]

        zeros = roots(f.ltrim(gen)).keys()

        if not zeros:
            return []

        if len(basis) == 1:
            return [ (zero,) for zero in zeros ]

        solutions = []

        for zero in zeros:
            new_system = []
            new_gens = gens[:-1]

            for b in basis[:-1]:
                eq = subs_root(b, gen, zero)

                if eq is not S.Zero:
                    new_system.append(eq)

            for solution in solve_reduced_system(new_system, new_gens):
                solutions.append(solution + (zero,))

        return solutions

    result = solve_reduced_system(polys, opt.gens, entry=True)

    if result is not None:
        return sorted(result)
    else:
        return None

def solve_triangulated(polys, *gens, **args):
    """
    Solve a polynomial system using Gianni-Kalkbrenner algorithm.

    The algorithm proceeds by computing one Groebner basis in the ground
    domain and then by iteratively computing polynomial factorizations in
    appropriately constructed algebraic extensions of the ground domain.

    Example
    =======

    >>> from sympy.solvers.polysys import solve_triangulated
    >>> from sympy.abc import x, y, z

    >>> F = [x**2 + y + z - 1, x + y**2 + z - 1, x + y + z**2 - 1]

    >>> solve_triangulated(F, x, y, z)
    [(0, 0, 1), (0, 1, 0), (1, 0, 0)]

    References
    ==========

    .. [Gianni89] Patrizia Gianni, Teo Mora, Algebraic Solution of System of
    Polynomial Equations using Groebner Bases, AAECC-5 on Applied Algebra,
    Algebraic Algorithms and Error-Correcting Codes, LNCS 356 247--257, 1989

    """
    G = groebner(polys, gens, polys=True)
    G = list(reversed(G))

    domain = args.get('domain')

    if domain is not None:
        for i, g in enumerate(G):
            G[i] = g.set_domain(domain)

    f, G = G[0].ltrim(-1), G[1:]
    dom = f.get_domain()

    zeros = f.ground_roots()
    solutions = set([])

    for zero in zeros:
        solutions.add(((zero,), dom))

    var_seq = reversed(gens[:-1])
    vars_seq = postfixes(gens[1:])

    for var, vars in zip(var_seq, vars_seq):
        _solutions = set([])

        for values, dom in solutions:
            H, mapping = [], zip(vars, values)

            for g in G:
                _vars = (var,) + vars

                if g.has_only_gens(*_vars) and g.degree(var) != 0:
                    h = g.ltrim(var).eval(mapping)

                    if g.degree(var) == h.degree():
                        H.append(h)

            p = min(H, key=lambda h: h.degree())
            zeros = p.ground_roots()

            for zero in zeros:
                if not zero.is_Rational:
                    dom_zero = dom.algebraic_field(zero)
                else:
                    dom_zero = dom

                _solutions.add(((zero,) + values, dom_zero))

        solutions = _solutions

    solutions = list(solutions)

    for i, (solution, _) in enumerate(solutions):
        solutions[i] = solution

    return sorted(solutions)


def is_zero_dimensional(G, *gens, **args):
    """
    Checks if the ideal generated by ``G`` is zero-dimensional (or,
    equivalently, if the number of solutions of the system ``G``
    is finite).
    In order to always obtain a correct result, ``G`` has to be a
    Groebner basis. However, if ``G`` is not a Groebner basis and
    ``True`` is returned, the ideal is zero-dimensional.

    For an ideal to be zero-dimensional, for every variable some
    power has to be the leading monomial of an element of ``G``.

    >>> from sympy import symbols
    >>> from sympy.polys.fglm import is_zero_dimensional
    >>> from sympy.polys import groebner
    >>> x, y, z = symbols('x, y, z')
    >>> F = [x**3 + x + 1, y**2 + 1, z - (x**2 + y)]
    >>> is_zero_dimensional(F, z, x, y, order='lex') # lucky choice!
    True
    >>> is_zero_dimensional(F, x, y, z, order='lex')
    False
    >>> G = groebner(F, x, y, z, order='grlex')
    >>> is_zero_dimensional(G, x, y, z, order='grlex')
    True

    References
    ==========

    Ideals, Varieties and Algorithms, David A. Cox, John B. Little,
    Donal O'Shea, 3rd edition, p. 234
    """
    options.allowed_flags(args, ['polys'])

    try:
        polys, opt = parallel_poly_from_expr(G, *gens, **args)
    except PolificationError, exc:
        raise ComputationFailed('is_zero_dimensional', len(G), exc)

    u = len(flatten(gens)) - 1

    def single_var(m):
        """Returns ``True`` if only a single entry of the tuple m is not ``0``. """
        n = 0
        for v in m:
            if v != 0:
                n += 1
        return n == 1

    # select leading monomials that are powers of a single variable
    leading_monomials = [g.LM(opt.order) for g in polys if single_var(g.LM(opt.order)) == True]

    exponents = [0] * (u + 1)

    for m in leading_monomials:
        exponents = map(lambda (e, f): e + f, zip(exponents, m))

    product = 1
    for e in exponents:
        product *= e

    return product != 0 #, product


def solve_generic2(polys, opt):
    """
    Solve system of polynomial equations ``polys`` in the ring
    `K[X_1, ..., X_n]` by computing a Groebner basis w.r.t. the
    specified order. If the system has infinitely many solutions an
    exception is raised, otherwise the characteristic polynomials of
    the linear maps from the vectorspace `K[X_1, ..., X_n]/(polys)`:

        ``f`` maps to ``X_i * f`` modulo ``polys``

    The roots of the characteristic polynomial are the i-th coordinates
    of the roots of ``polys``.
    This approach has the advantage that errors from numerical
    computation are not propagated and that only a Groebner basis
    w.r.t. for example ``grevlex`` need to be computed.

    References
    ==========

    .. David A. Cox, John Little, Donal O'Shea, Using Algebraic Geometry,
    2nd edition, p. 56-60
    """

    def k_basis(G, gens, order, domain):
        """
        Find a `K`-basis of ``K[X_1, ..., X_n]/(G)``. One such basis
        are the monomials `X^\alpha` which are not divisible by
        leading monomials of ``G``. This set is finite if and only
        if the ideal generated by ``G`` is zero-dimensional.
        """
        basis = []
        candidates = [Poly(domain.one, gens, domain=domain)]
        
        while candidates:
            t = candidates.pop()
            basis.append(t)

            new_candidates = [t * Poly(v, gens, domain=domain) for v in gens]
            new_candidates = [m for m in new_candidates if all([monomial_div(m.LM(order), g.LM(order)) is None for g in G])]
            candidates.extend(new_candidates)
            candidates.sort(key=lambda m: monomial_key(order)(m.LM(order)), reverse=True)
        basis = set(basis)
        basis = list(basis)
        return sorted(basis, key=lambda f: monomial_key(order)(f.LM(order)))

    def normalform(f, G, order):
        r = Poly(0, f.gens)
        while not f.is_zero:
            for g in G:
                if monomial_div(f.LM(order), g.LM(order)) is not None:
                    ltf = f.as_expr().as_ordered_terms(order)[0]
                    ltg = g.as_expr().as_ordered_terms(order)[0]

                    f = f - Poly(ltf/ltg, f.gens) * g
                    break
            else:
                ltf = f.as_expr().as_ordered_terms(order)[0]
                r = r + Poly(ltf, f.gens)
                f = f - Poly(ltf, f.gens)

        return r

    def representing_matrix(m, basis, G, order, domain):
        """
        Computes the matrix `M_m` representing the multiplication by
        ``m`` in `K[X_1, ... X_n]/(G)` w.r.t. the basis ``basis``
        (sorted w.r.t. ``order``), consisting of monomials not
        divisibly by the leading monomials of ``G``.
        """
        basis_monomials = [b.monoms()[0] for b in basis]
        M = zeros((len(basis), len(basis)))
        non_zero = 0

        for i, v in enumerate(basis):
            r = normalform(Poly(m) * v, G, order)

            for term in r.terms():
                j = basis_monomials.index(term[0])
                M[i, j] = term[1]
                non_zero += 1

        return M, float(non_zero)/len(basis)**2

    G = groebner(polys, opt.gens, order="grlex", polys=True)

    if not is_zero_dimensional(G, opt.gens, order="grlex", polys=True):
        raise NotImplementedError("only zero-dimensional systems supported (finite number of solutions)")

    basis = k_basis(G, opt.gens, "grlex", opt.domain)
    coordinates = []
    t = Dummy('t')

    for v in opt.gens:
        M, sparsity = representing_matrix(v, basis, G, "grlex", opt.domain)
        coordinates.append(M.eigenvals().keys())

        if [] in coordinates:
            raise ComputationFailed("Can't express roots of characteristic polynomial as radicals")

    candidates = [tuple(s) for s in product(*coordinates)]

    # filter candidates that evaluate to zero for all p in polys
    def is_zero(p, F, gens):
        """
        Check if ``p`` is a zero of ``F``.
        """
        for f in F:
            # this has to be done numerically, since simplification is not powerful enough
            if abs(N(f.subs(dict(zip(gens, p))))) > 1e-10:
                return False
        return True

    solutions = [c for c in candidates if is_zero(c, polys, opt.gens)]
    return solutions
