
from functools import reduce
from string import Template

from sympy import *

def make_recurrence_spec(**kwds):
    assert  'recurrence_eq' in kwds and \
            'index' in kwds and \
            'indexed' in kwds and \
            'terms_cache' in kwds, "Missed key in making recurrence spec"
    return kwds

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


def unfold_recurrence(recurrence_spec, unfolding_recurrence_spec=None):

    if not unfolding_recurrence_spec: unfolding_recurrence_spec = recurrence_spec

    def worker(recurrence_eq, unfolding_recurrence_eq, indexed, index, terms_cache):

        def linear_matcher(subscript, variable):
            
            a_wild, b_wild = Wild('a', exclude=[variable]), Wild('b', exclude=[variable])
            matched = subscript.match(a_wild*variable + b_wild)
            
            if not matched: return None
            
            a, b = matched[a_wild], matched[b_wild]
            normalizer = lambda term: term.replace(variable, (variable - b)/a)
           
            return normalizer


        def unfolding(rhs_term):
            
            if indexed.args[0] not in rhs_term.free_symbols: return rhs_term
            elif rhs_term in terms_cache: return terms_cache[rhs_term]
            
            matched_lhs_term = take_apart_matched(recurrence_eq.lhs, indexed)
            lhs_normalizer = linear_matcher(matched_lhs_term['subscript'], index)
            norm_lhs = lhs_normalizer(recurrence_eq.lhs)

            matched_rhs_term = take_apart_matched(rhs_term, indexed)
            unfolded_term = rhs_term

            if matched_rhs_term:
                
                subs_lhs = norm_lhs.replace(index, matched_rhs_term['subscript'])
                matched_subs_lhs_term = take_apart_matched(subs_lhs, indexed)

                # since subscripts are equal by substitution, we have to check coefficients
                assert matched_subs_lhs_term['subscript'] == matched_rhs_term['subscript']

                if matched_subs_lhs_term['coeff'] == matched_rhs_term['coeff']:
                    rebuilt_rhs_term = lhs_normalizer(recurrence_eq.rhs)
                    unfolded_term = rebuilt_rhs_term.replace(index, matched_rhs_term['subscript'])
                    terms_cache[rhs_term] = unfolded_term

            if rhs_term not in terms_cache:
                    matched_norm_lhs = take_apart_matched(norm_lhs, indexed)
                    generalized_rhs_term = Mul(lhs_normalizer(recurrence_eq.rhs), 
                        Integer(1)/matched_norm_lhs['coeff'])

                    substitutions = {}
                    
                    for subscript in indexed_terms_appearing_in(
                            rhs_term, indexed, only_subscripts=True, do_traversal=True):
                    
                        subscripted_term = indexed[subscript]
                        if subscripted_term not in substitutions and subscripted_term not in terms_cache:
                            subterm = generalized_rhs_term.replace(index, subscript)
                            substitutions.update({subscripted_term: subterm})

                    terms_cache.update(substitutions)
                    unfolded_term = rhs_term.subs(terms_cache, simultaneous=True)
                    
                
            return unfolded_term    
            
        unfolded_rhs_terms = map(unfolding, flatten(unfolding_recurrence_eq.rhs.args, cls=Add))
        
        folded_rhs_term = reduce(   lambda folded, addend: Add(folded, addend, evaluate=False), 
                                    unfolded_rhs_terms)
        
        return dict(recurrence_eq=Eq(recurrence_eq.lhs, folded_rhs_term),
                    indexed=indexed,
                    index=index,
                    terms_cache=terms_cache)

    return worker(  recurrence_spec['recurrence_eq'],
                    unfolding_recurrence_spec['recurrence_eq'],
                    unfolding_recurrence_spec['indexed'],
                    unfolding_recurrence_spec['index'],
                    unfolding_recurrence_spec['terms_cache'].copy())

def indexed_terms_appearing_in(term, indexed, only_subscripts=False, do_traversal=False):

    indexed_terms_set = set()

    subterms_iter = preorder_traversal(term) if do_traversal else flatten(term.args, cls=Add)

    for subterm in subterms_iter:
        matched = take_apart_matched(subterm, indexed)
        if not matched: continue
        subscript = matched['subscript']
        indexed_terms_set.add(subscript if only_subscripts else indexed[subscript])

    return indexed_terms_set


def factor_rhs_unfolded_rec(unfolded_recurrence_spec):

    unfolded_recurrence_eq = unfolded_recurrence_spec['recurrence_eq']

    indexed_terms_in_rec = indexed_terms_appearing_in(
        unfolded_recurrence_eq.rhs, unfolded_recurrence_spec['indexed'])

    factored_spec = dict(**unfolded_recurrence_spec)
    factored_spec.update(recurrence_eq=Eq(unfolded_recurrence_eq.lhs, 
        Poly(unfolded_recurrence_eq.rhs, *list(indexed_terms_in_rec)).args[0]))

    return factored_spec

def do_unfolding_steps(recurrence_spec, steps=1, factor_rhs=False, 
                        keep_intermediate_unfoldings=False, first_order=True):
        
    def first_order_reducer(working_recurrence_spec_folded, step): 

        unfoldings, working_recurrence_spec = working_recurrence_spec_folded

        unfolded_spec = unfold_recurrence(recurrence_spec, working_recurrence_spec)
        unfoldings.update({step:unfolded_spec})

        return unfoldings, unfolded_spec
    
    def second_order_reducer(working_recurrence_spec_folded, step): 

        unfoldings, working_recurrence_spec = working_recurrence_spec_folded

        unfolded_spec = unfold_recurrence(working_recurrence_spec, working_recurrence_spec)
        unfoldings.update({step:unfolded_spec})

        return unfoldings, unfolded_spec

    unfoldings, unfolded_recurrence_spec = reduce(
        first_order_reducer if first_order else second_order_reducer, 
        range(steps), ({}, recurrence_spec))
    
    result = None
    if keep_intermediate_unfoldings:
        result = {k:factor_rhs_unfolded_rec(v) for k,v in unfoldings.items()} \
            if factor_rhs else unfoldings
    else:
        result = factor_rhs_unfolded_rec(unfolded_recurrence_spec) \
            if factor_rhs else unfolded_recurrence_spec

    return result


def base_instantiation(unfolded_recurrence_spec, base_index=0):

    def worker(recurrence_eq, indexed, index, terms_cache):

        rhs = recurrence_eq.rhs
        rhs_summands = flatten(rhs.args, cls=Add)
        
        def subscript_equation_maker(rhs_term):
            
            matched = take_apart_matched(rhs_term, indexed)
            
            return Eq(matched['subscript'], base_index) if matched else None
        
        valid_equations = filter(lambda x: False if x is None else True, 
                                 map(subscript_equation_maker, rhs_summands))
        
        solutions = map(lambda eq: take_sol(eq, index), valid_equations)
        
        satisfying_index = max(solutions)

        def subs_index_into(term): return term.subs(index, satisfying_index)

        new_terms_cache = {subs_index_into(k):subs_index_into(v)
                            for k,v in terms_cache.items()}

        return dict(recurrence_eq=subs_index_into(recurrence_eq),
                    indexed=indexed,
                    index=satisfying_index,
                    terms_cache=new_terms_cache)

    return worker(**unfolded_recurrence_spec)

def project_recurrence_spec(recurrence_spec, **props):
    
    projected = []
    for k,v in props.items(): 
        if v and k in recurrence_spec: projected.append(recurrence_spec[k])

    return projected[0] if len(projected) == 1 else tuple(projected)


def times_higher_order_operator(recurrence_spec, 
        times_range=range(6), 
        operator=lambda *args: tuple(args), 
        instantiate=True, 
        include_last_terms_cache=False,
        first_order=True):

    initial_terms_cache = recurrence_spec['terms_cache'].copy()

    def worker(working_steps):

        unfolded_evaluated_spec = do_unfolding_steps(
            recurrence_spec, working_steps, factor_rhs=True, 
            first_order=first_order)

        recurrence_spec['terms_cache'].update(unfolded_evaluated_spec['terms_cache'])

        processed_recurrence_spec = unfolded_evaluated_spec
        if instantiate: processed_recurrence_spec = base_instantiation(processed_recurrence_spec)

        return operator(processed_recurrence_spec, working_steps)

    mapped = map(worker, times_range)

    last_terms_cache = recurrence_spec['terms_cache'].copy()
    recurrence_spec['terms_cache'] = initial_terms_cache

    return (mapped, last_terms_cache) if include_last_terms_cache else mapped 


def repeated_instantiating(base_instantiated_rec_spec):
    
    def worker(previous_terms_cache, do_one_more_step):
    
        if not do_one_more_step: return previous_terms_cache
        else: do_one_more_step = False
            
        def subterm_mapping(subterm):    
                
            nonlocal do_one_more_step
            new_subterm = subterm
            
            if subterm.free_symbols:
                new_subterm = subterm.subs(previous_terms_cache)
                if subterm != new_subterm: do_one_more_step = True
                
            return new_subterm
            
        current_terms_cache = { k:subterm_mapping(v) for k,v in previous_terms_cache.items() }
        
        return worker(current_terms_cache, do_one_more_step)

    
    fully_instantiated_terms_cache = worker(base_instantiated_rec_spec['terms_cache'], 
                                            do_one_more_step=True)
    
    fully_instantiated_rec_eq = base_instantiated_rec_spec['recurrence_eq'].subs(
        fully_instantiated_terms_cache)
    
    return dict(recurrence_eq=fully_instantiated_rec_eq, 
                indexed=base_instantiated_rec_spec['indexed'],
                index=base_instantiated_rec_spec['index'],
                terms_cache=fully_instantiated_terms_cache)

def take_sol(*args, sol_index=0):
    sols = solve(*args)
    return sols[sol_index]

def subsume_cache(recurrence_spec):

    recurrence_eq, index, indexed, terms_cache = (
        recurrence_spec['recurrence_eq'], 
        recurrence_spec['index'], 
        recurrence_spec['indexed'], 
        recurrence_spec['terms_cache'])

    subsumed_rec_specs = {}

    for k,v in terms_cache.items():
        kv_eq = Eq(k, v)
        matched_key = take_apart_matched(k, indexed)
        if matched_key and index in matched_key['subscript'].free_symbols:
            subscript, dummy_sym = matched_key['subscript'], Dummy()
            sol = take_sol(Eq(subscript, dummy_sym), index).subs(dummy_sym, index)
            subsumed_eq = kv_eq.subs(index, sol)
            subsumed_rec_specs.update({subsumed_eq: make_recurrence_spec(
                recurrence_eq=subsumed_eq, index=index, indexed=indexed, terms_cache={})})
        else: 
            subsumed_rec_specs.update({kv_eq: make_recurrence_spec(
                recurrence_eq=kv_eq, index=index, indexed=indexed, terms_cache={})})

    return subsumed_rec_specs.values()

def to_matrix_notation(eqs, indexed, order):

    lhs_vector = []
    comb_dicts = [] 
    
    def worker(eq):

        lhs_vector.append(eq.lhs)

        comb_dict = {}
        if isinstance(eq.rhs, Add):
            for summand in flatten(eq.rhs.args, cls=Add):
                matched = take_apart_matched(summand, indexed)
                if matched: comb_dict.update( { matched['subscript']: matched['coeff'] } )
                #else: print(summand)
        else:
            matched = take_apart_matched(eq.rhs, indexed)
            if matched: comb_dict.update( { matched['subscript']: matched['coeff'] } )

        comb_dicts.append(comb_dict)

    for eq in eqs: worker(eq)

    rows = len(comb_dicts)
    comb_vector = Matrix([indexed[o] for o in order])
    cols = len(comb_vector[:,0])
    comb_matrix = zeros(rows, cols)
    
    for r in range(rows):
        for c in range(cols):
            comb_dict, k = comb_dicts[r], order[c]
            if k in comb_dict: comb_matrix[r, c] = comb_dict[k]

    #return Eq(Mul(comb_matrix, comb_vector, evaluate=False), Matrix(lhs_vector), evaluate=False)
    return comb_matrix, comb_vector, Matrix(lhs_vector)

def invert_dict(a_dict, check_bijection=True):

    inverted = {}
    
    if check_bijection:
        for k,v in a_dict.items():
            if v in inverted: raise Exception("v is mapped at least by k and inverted[v], not a bijection")
            inverted.update({v:k})
    else:
        inverted.update({v:k for k,v in a_dict.items()})

    return inverted


def latex_array_env(*args, **kwd):
    
    def eqnarray_entry_for_eq(processed_spec, working_steps):
        processed_eq = project_recurrence_spec(processed_spec, recurrence_eq=True)
        return latex(processed_eq) + r"\\"

    mapped = times_higher_order_operator(*args, operator=eqnarray_entry_for_eq, **kwd)
    template = Template(r"""\begin{array}{c}$content\end{array}""")

    return template.substitute(content="\n".join(mapped))


def ipython_latex(*args, **kwd):
    
    from IPython.display import Latex
    return Latex(latex_array_env(*args, **kwd))
