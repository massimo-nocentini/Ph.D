
from functools import reduce

def take_apart_matched(term, indexed):
    
    wild_coeff = Wild('coeff', exclude=[indexed])
    wild_term, wild_subscript = Wild('term'), Wild('subscript')

    matched_term = term.match(wild_coeff * wild_term)

    result = None

    if matched_term: 
        coeff, indexed_term = matched_term[wild_coeff], matched_term[wild_term]
        matched_term_subscript = indexed_term.match(indexed[wild_subscript])
        if matched_term_subscript:
            term_subscript = matched_term_subscript[wild_subscript]
            result = {'coeff':coeff, 'subscript':term_subscript}

    return result


def unfold_recurrence(recurrence_eq, unfolding_recurrence_eq, indexed, index, 
                      terms_cache={}, evaluate=False):

    def unfolding(rhs_term):
        
        if rhs_term in terms_cache: return terms_cache[rhs_term]
        
        matched_rhs_term = take_apart_matched(rhs_term, indexed)
        unfolded_term = rhs_term
        
        if matched_rhs_term:
            
            matched_lhs_term = take_apart_matched(recurrence_eq.lhs, indexed)
        
            def match_linear(subscript, variable):
                
                a_wild, b_wild = Wild('a', exclude=[variable]), Wild('b', exclude=[variable])
                matched = subscript.match(a_wild*variable + b_wild)
                
                if not matched: return None
                
                a, b = matched[a_wild], matched[b_wild]
                normalizer = lambda term: term.replace(variable, variable - (b/a))
               
                return normalizer
            
            lhs_normalizer = match_linear(matched_lhs_term['subscript'], index)
            
            norm_lhs = lhs_normalizer(recurrence_eq.lhs)
            subs_lhs = norm_lhs.replace(index, matched_rhs_term['subscript'])
            matched_subs_lhs_term = take_apart_matched(subs_lhs, indexed)
            # since subscripts are equal by substitution, we have to check coefficients
            assert matched_subs_lhs_term['subscript'] == matched_rhs_term['subscript']
            if matched_subs_lhs_term['coeff'] == matched_rhs_term['coeff']:
                rebuilt_rhs_term = lhs_normalizer(recurrence_eq.rhs)
                unfolded_term = rebuilt_rhs_term.replace(index, matched_rhs_term['subscript'])
                terms_cache[rhs_term] = unfolded_term
            
        return unfolded_term    
        
    unfolded_rhs_terms = map(unfolding, flatten(unfolding_recurrence_eq.rhs.args, cls=Add))
    
    folded_rhs_term = reduce(lambda folded, addend: Add(folded, addend, evaluate=False), unfolded_rhs_terms)
    
    return Eq(recurrence_eq.lhs, folded_rhs_term)

def evaluate_unfolded_rec(unfolded_recurrence):
    return Eq(unfolded_recurrence.lhs, Poly(unfolded_recurrence.rhs).args[0])

def do_unfolding_steps(recurrence, steps=1, terms_cache={}, **options):
    
    recurrence_eq, c, n = recurrence
    
    #if 'terms_cache' not in options: 
    #    terms_cache = {}
    #    options['terms_cache']=terms_cache
        
    def reducer(working_recurrence_eq, step): 
        return unfold_recurrence(recurrence_eq, working_recurrence_eq, c, n, terms_cache, **options)

    unfolded_recurrence = reduce(reducer, range(steps), recurrence_eq)
    evaluate = 'evaluate' in options and options['evaluate']
    
    return evaluate_unfolded_rec(unfolded_recurrence) if evaluate else unfolded_recurrence

def base_instantiation(unfolded_recurrence_eq, indexed, variable):
    
    rhs = unfolded_recurrence_eq.rhs
    rhs_summands = flatten(rhs.args, cls=Add)
    
    def subscript_equation_maker(rhs_term):
        
        matched = take_apart_matched(rhs_term, indexed)
        
        return Eq(matched['subscript'],0) if matched else None
    
    valid_equations = filter(lambda x: False if x is None else True, 
                             map(subscript_equation_maker, rhs_summands))
    
    solutions = map(lambda eq: solve(eq, variable)[0], valid_equations)
    
    return unfolded_recurrence_eq.subs(variable, max(solutions))


