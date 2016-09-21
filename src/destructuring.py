
from sympy import Wild, Indexed
from contextlib import contextmanager

class DestructuringError(ValueError): 
    '''
    Represent an error due to the impossibility to destructure a given term.

    At the present, we neither provide meaningful error messages nor objects
    related to the context in which this exception was raised; moreover, we
    do not distinguish the operator in the tackled combination term (Add, Mul,...).
    '''

    pass

# only for keep the same api, delete it when refactoring is finished,
# a good name to use could be: "destructuring_monomial_with_coeff_subscripts"
@contextmanager
def bind_Mul_indexed(term, indexed, forbidden_terms=[]):
    '''
    Destructure `term` against pattern `coeff * f[i j ...]`, binding `coeff`, `i` and `j ...`.

    I attempt to destructure the given term respect the `Mul` operator, aiming to isolate
    term `indexed`, which should be an instance of `Indexed` class, from a coefficient `coeff`,
    which collect everything but `indexed` and, optionally, objects appearing in `forbidden_terms`.
    If such destructuring fails, then I raise `DestructuringError`.

    Examples
    ========
    
    >>> from sympy import *

    Main track, everything is good:
    >>> f, n, k, j = IndexedBase('f'), *symbols('n k j')
    >>> term = 3 * f[n,k,j]
    >>> with bind_Mul_indexed(term, f) as (coeff, subscripts):
    ...     print('{} * {}'.format(coeff, subscripts))
    3 * [n, k, j]
    
    Failure, not a vanilla product:
    >>> term = 3 * f[n] + 1
    >>> try:
    ...     with bind_Mul_indexed(term, f) as (coeff, subscripts):
    ...         print('{} * {}'.format(coeff, subscripts))
    ... except DestructuringError:
    ...     print('something else')
    something else

    Failure, `f` not indexed at all:
    >>> term = 3 * f
    >>> try:
    ...     with bind_Mul_indexed(term, f) as (coeff, subscripts):
    ...         print('{} * {}'.format(coeff, subscripts))
    ... except DestructuringError:
    ...     print('something else')
    something else
    '''

    coeff_w, ind_w = Wild('coeff', exclude=[indexed] + forbidden_terms), Wild('ind')
    matched = term.match(coeff_w * ind_w)
    # if no indexing applied then `isinstance(matched[ind_w], IndexedBase)` holds
    if (matched 
        and ind_w in matched 
        and coeff_w in matched 
        and isinstance(matched[ind_w], Indexed)):
        _, *subscripts = matched[ind_w].args
        yield matched[coeff_w], subscripts # do not splice subscripts, give them packed
    else:
        raise DestructuringError()
