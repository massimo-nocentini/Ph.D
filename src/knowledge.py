
from utils import invert_dict
from sympy import IndexedBase, fibonacci

def fibonacci_numbers(start=0, limit=100, symbolic_keys=True):
    f = IndexedBase('f')
    return {(f[i] if symbolic_keys else i):fibonacci(i) for i in range(start, limit)}

def fibonacci_numbers_inverted_mapping(**kwds):
    if 'start' not in kwds: kwds['start'] = 2
    return  invert_dict(fibonacci_numbers(**kwds))
