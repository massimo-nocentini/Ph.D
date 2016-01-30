
from sympy import *

def expand_Sum(aSumExpr):
    
    generic_sum_coeff, (sum_index, starting_bound, ending_bound) = aSumExpr.args
    
    result = None
    
    if starting_bound.free_symbols:
        result = lambda **symbols: expand_Sum(aSumExpr.func(generic_sum_coeff, 
                                                (sum_index, starting_bound.subs(symbols), ending_bound)))
    elif ending_bound.free_symbols:
        result = lambda **symbols: expand_Sum(aSumExpr.func(generic_sum_coeff, 
                                                (sum_index, starting_bound, ending_bound.subs(symbols))))
    elif ending_bound.is_infinite: 
        
        result = aSumExpr
        
        '''
        def splitter(new_symbol):
            new_term_for_expansion = aSumExpr.func(generic_sum_coeff,
                                                    (sum_index, starting_bound, new_symbol))
            rest_of_infinite_term = aSumExpr.func(generic_sum_coeff,
                                                    (sum_index, new_symbol+1, ending_bound))
            expanded_new_term = expand_Sum(new_term_for_expansion)
            return Add(expanded_new_term, rest_of_infinite_term, evaluate=False)
        
        result = splitter
        '''
    else:    
        summands = [generic_sum_coeff.subs(sum_index, n) for n in range(starting_bound, ending_bound+1)]
        result = Add(*summands, evaluate=False)
        
    return result

