
from sympy import flatten, Add

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

