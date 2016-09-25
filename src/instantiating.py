
from sympy import Dummy

class raw:

    def __init__(self, substitutions):
        self.substitutions = substitutions

class based:

    def __init__(self, arity):
        self.arity = arity

class unary_indexed: 

    def __init__(self, base_index=[0]):
        self.base_index = base_index

class doubly_indexed: 

    def __init__(self, base_index=[None, 0]):
        _, k_index = base_index
        self.base_index = [Dummy(), k_index]
