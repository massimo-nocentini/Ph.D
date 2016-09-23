
from sympy import flatten, Add, preorder_traversal
from destructuring import *

def explode_term_respect_to(term, cls, deep=False):

    exploded = [term] # we start with the given term since we've to build a list, eventually

    if isinstance(term, cls): 
        exploded = flatten(term.expand().args, cls=cls) if deep else term.args

    return exploded

def not_evaluated_Add(*args, **kwds):
    '''
    Build an `Add` object, *not evaluated*, regardless any value for the keyword `evaluate`.
    '''
    kwds['evaluate']=False # be sure that evaluation doesn't occur
    return Add(*args, **kwds)

def symbol_of_Indexed(indexed):
    '''
    Return the `Symbol` object of an indexable term, otherwise return the given argument as is.

    To be honest, any iterable with at least one element works; maybe we should do `isinstance(...)`
    checks to properly implement this function.
    '''

    try:
        indexed_sym, *rest = indexed.args
        result = indexed_sym
    except Exception:
        result = indexed

    return result

def indexed_terms_appearing_in(term, indexed, only_subscripts=False, do_traversal=False):

    indexed_terms_set = set()

    for subterm in preorder_traversal(term) if do_traversal else flatten(term.args, cls=Add):
        try:
            with bind_Mul_indexed(subterm, indexed) as (_, subscripts):
                indexed_terms_set.add(subscripts if only_subscripts else indexed[subscripts])
        except DestructuringError:
            continue

    return list(indexed_terms_set)
