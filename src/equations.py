
from contextlib import contextmanager
from sympy import Dummy, solve, Eq

@contextmanager
def isolated_lhs_normal_form(eq, subscripts_rel):
    '''
    Normal form of an equation isolating subscripts in its `lhs`.

    I consume an `Eq` object and, assuming in the `lhs` there's a term that defines the `rhs`,
    then I return an `Eq` object such that subscripts are in vanilla form, ie. where 
    no offsets appear in the lhs.

    Examples
    ========
    
    >>> from sympy import *

    Main track, everything is good:
    >>> f, n, k = IndexedBase('f'), *symbols('n k')
    >>> n_subscript, k_subscript = n+3, 2*k-1
    >>> rhs = log(n)+k/2
    >>> eq = Eq(f[n_subscript, k_subscript], rhs)
    >>> eq
    Eq(f[n + 3, 2*k - 1], k/2 + log(n))
    >>> subscripts_rel = [(n, n_subscript), (k, k_subscript)]
    >>> with isolated_lhs_normal_form(eq, subscripts_rel) as eq_in_nf: print(eq_in_nf)
    Eq(f[n, k], k/4 + log(n - 3) + 1/4)

    '''

    normalized = eq
    for var, comb in subscripts_rel.items():
        d = Dummy()
        sol = solve(Eq(comb, d), var).pop()
        normalized = normalized.subs(var, sol).subs(d, var)

    yield normalized

@contextmanager
def instantiate_eq(eq, constraints):
    '''
    Instantiate the given `Eq` object according to the given constraints.

    Substitutions happen *not* simultaneously, therefore another implementation
    is possible using the capabilities of `subs`, namely:
        `eq.subs(constraints, simultaneous=True)`
    '''
    instantiated = eq
    for var, rel in constraints.items():
        instantiated = instantiated.subs(var, rel)
    yield instantiated
