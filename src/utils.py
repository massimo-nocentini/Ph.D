
import functools
from contextlib import contextmanager



@contextmanager
def map_reduce(on, doer, reducer, initializer=None):
    '''
    Map-Reduce pipeline.
    '''
    yield functools.reduce(reducer, map(doer, on), initializer)



@contextmanager
def fmap_on_dict(doer, on, on_key=True, on_value=True):
    '''
    Apply `doer` to the given mapping, inspired to `Functor`s in Haskell.

    It is possible to choose to apply `doer` to both (key, value) pair or only partially.
    '''
    yield {(doer(k) if on_key else k): (doer(v) if on_value else v) for k,v in on.items()}

@contextmanager
def bind(*args, single=False):
    yield args[0] if single else args
