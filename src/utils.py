
import functools
from contextlib import contextmanager
from functools import partial



@contextmanager
def map_reduce(on, doer, reducer, initializer=None):
    '''
    Map-Reduce pipeline.
    '''
    yield functools.reduce(reducer, map(doer, on), initializer)



@contextmanager
def fmap_on_dict(on, key_doer=lambda k: k, value_doer=lambda v: v, 
                 also_for_values=False, also_for_keys=False):
    '''
    Apply `doer` to the given mapping, inspired to `Functor`s in Haskell.

    It is possible to choose to apply `doer` to both (key, value) pair or only partially.
    '''
    if key_doer and also_for_values: value_doer = key_doer
    elif value_doer and also_for_keys: key_doer = value_doer

    yield {key_doer(k): value_doer(v) for k,v in on.items()}

@contextmanager
def bind(*args, single=False):
    yield args[0] if single else args


class dispatch_message:

    def __init__(self, variety, target):
        self.variety = variety
        self.target = target
    
    def __getattr__(self, name): 
        dispatched_name = '_{}_by_{}'.format(name, type(self.variety).__name__)
        return partial(getattr(self.target, dispatched_name), dispatcher=self.variety)
        
