
import functools
from copy import copy
from contextlib import contextmanager

from sympy import *


class DestructuringError(ValueError): 
    '''
    Represent an error due to the impossibility to destructure a given term.

    At the present, we neither provide meaningful error messages nor objects
    related to the context in which this exception was raised; moreover, we
    do not distinguish the operator in the tackled combination term (Add, Mul,...).
    '''

    pass

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
    if (matched and ind_w in matched and coeff_w in matched 
            and isinstance(matched[ind_w], Indexed)):
        _, *subscripts = matched[ind_w].args
        yield matched[coeff_w], subscripts # do not splice subscripts, give them structured
    else:
        raise DestructuringError()


def explode_term_respect_to(term, op_class, deep=False):

    exploded = [term] # at least we start with the given term since we've to build a list eventually

    if isinstance(term, op_class): 
        exploded = flatten(term.expand().args, cls=op_class) if deep else term.args

    return exploded

def not_evaluated_Add(*args, **kwds):
    '''
    Build an `Add` object, *not evaluated*, regardless any value for the keyword `evaluate`.
    '''
    kwds['evaluate']=False # be sure that evaluation doesn't occur
    return Add(*args, **kwds)

def symbol_of_indexed(indexed):
    '''
    Return the `Symbol` object of an indexable term, otherwise return the given argument as is.
    '''
    return indexed.args[0] if (isinstance(indexed, Indexed) 
        or isinstance(indexed, IndexedBase)) else indexed

@contextmanager
def map_reduce(on, doer, reducer, initializer=None):
    yield functools.reduce(reducer, map(doer, on), initializer)

@contextmanager
def normalize_eq(eq, constraints):
    normalized = eq
    for var, rel in constraints.items():
        d = Dummy()
        sol = solve(Eq(rel, d), var).pop()
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

@contextmanager
def copy_recurrence_spec(recurrence_spec):
    '''
    Build a shallow copy of the given recurrence spec, `terms_cache` is a shallow copy too.
    '''
    yield recurrence_spec._replace(terms_cache=copy(recurrence_spec.terms_cache))























