
import copy
from functools import reduce
from string import Template

from sympy import *
from sympy.printing.latex import latex

from utils import *

from destructuring import *
from equations import *
from terms import *


class recurrence_spec:

    def __init__(self, recurrence_eq, recurrence_symbol, variables, terms_cache={}):
        self.recurrence_eq = recurrence_eq
        self.indexed = recurrence_symbol
        self.index = variables # rename to `indexes`
        self.terms_cache = terms_cache
        
    def description(self, include_terms_cache=False, doit=False):
        from IPython.display import Markdown
        src = 'Recurrence formal symbol ${fs}$, indexed by ${variables}$, in relation:\n\n$${eq}$$'
        src = src.format(   fs=latex(self.indexed), 
                            variables=", ".join(map(latex, self.index)), 
                            eq=latex(self.recurrence_eq.doit() if doit else self.recurrence_eq))

        if include_terms_cache and self.terms_cache: 
            src += "\n\nwith unfolded terms:\n\n$${terms}$$".format(terms=
                    latex({Eq(k, v) for k, v in self.terms_cache.items()}))

        return Markdown(src)


    def unfold(self, depth=1, first_order=True):
            
        def first_order_reducer(folding_recurrence_spec, step): 
            return folding_recurrence_spec.rewrite(according_to=self)
        
        def second_order_reducer(folding_recurrence_spec, step):
            return folding_recurrence_spec.rewrite(according_to=folding_recurrence_spec)

        unfolded_recurrence_spec = reduce(
            first_order_reducer if first_order else second_order_reducer, 
            range(depth), self)
        
        return unfolded_recurrence_spec

    def rewrite(self, according_to):


        eq, index, indexed = according_to.recurrence_eq, according_to.index, according_to.indexed
        unfolding_recurrence_eq, terms_cache = self.recurrence_eq, copy.copy(self.terms_cache)

        # the following normal form could be computed in the ctor?
        with    bind_Mul_indexed(eq.lhs, indexed) as (coeff, subscripts), \
                bind(dict(zip(index, subscripts)), single=True) as subscripts_rel, \
                isolated_lhs_normal_form(eq, subscripts_rel) as eq_in_nf:
                    normalized_eq = eq_in_nf

        def unfolding(rhs_term):
            

            if symbol_of_Indexed(indexed) not in rhs_term.free_symbols: return rhs_term
            elif rhs_term in terms_cache: return terms_cache[rhs_term]

            with    bind_Mul_indexed(rhs_term, indexed) as (coeff, subscripts), \
                    bind(dict(zip(index, subscripts)), single=True) as constraints, \
                    instantiate_eq(normalized_eq, constraints) as instantiated_eq, \
                    bind_Mul_indexed(instantiated_eq.lhs, indexed) as (coeff_lhs, _):

                    # if coeff == coeff_lhs then we've a perfect match for unfolding
                    unfolded_term = instantiated_eq.rhs * (coeff/coeff_lhs)

                    # here we could perform a simplification using:
                    #simplified_eq = Eq(rhs_term, unfolded_term).simplify() 
                    #terms_cache[simplified_eq.lhs] = simplified_eq.rhs
                    terms_cache[rhs_term] = unfolded_term

                    return unfolded_term    
            
        rhs_terms = explode_term_respect_to(unfolding_recurrence_eq.rhs, cls=Add, deep=True)
        with map_reduce(on=rhs_terms, doer=unfolding, 
                        reducer=lambda reduced, term: not_evaluated_Add(reduced, term), 
                        initializer=Integer(0)) as folded_rhs_term:
            return recurrence_spec(recurrence_eq=Eq(unfolding_recurrence_eq.lhs, folded_rhs_term), 
                                   recurrence_symbol=indexed, 
                                   variables=index, 
                                   terms_cache=terms_cache)

    def factor(self, *gens, **kwds):

        eq = self.recurrence_eq
        rhs = factor(eq.rhs, *gens, **kwds)

        return recurrence_spec( recurrence_eq=Eq(eq.lhs, rhs),
                                recurrence_symbol=self.indexed,
                                variables=self.index,
                                terms_cache=copy.copy(self.terms_cache))  

    def subsume(self, additional_terms={}):

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
                
            with fmap_on_dict(  on=previous_terms_cache, 
                                value_doer=subterm_mapping, 
                                also_for_keys=False) as current_terms_cache:
                return worker(current_terms_cache, do_one_more_step)

        
        additional_terms.update(self.terms_cache)
        subsumed_terms_cache = worker(additional_terms, do_one_more_step=True)

        return recurrence_spec( recurrence_eq=self.recurrence_eq,
                                recurrence_symbol=self.indexed,
                                variables=self.index,
                                terms_cache=subsumed_terms_cache)

    def instantiate(self, strategy):

        solutions = strategy.dispatch_instantiate_on(target=self)

        def subs_sols_into(term): 
            return term.subs(solutions, simultaneous=True)

        with fmap_on_dict(  on=self.terms_cache, 
                            key_doer=subs_sols_into, 
                            also_for_values=True) as new_terms_cache:

            return recurrence_spec(recurrence_eq=subs_sols_into(self.recurrence_eq),
                        recurrence_symbol=self.indexed, 
                        variables=solutions, terms_cache=new_terms_cache)

    def _instantiate_by_raw(self, dispatcher):
        return dispatcher.substitutions

    def _instantiate_by_based(self, dispatcher):

        valid_equations = []

        rhs_summands = explode_term_respect_to(self.recurrence_eq.rhs, cls=Add, deep=True)
        for rhs_term in rhs_summands:
            try:
                with bind_Mul_indexed(rhs_term, self.indexed) as (_, subscripts):
                    eqs = {var: solve(Eq(base, rel), var).pop() 
                           for var, base, rel in zip(self.index, 
                                                     dispatcher.arity.base_index, 
                                                     subscripts)} 
                    valid_equations.append(eqs)
            except DestructuringError: 
                continue
        
        return dispatcher.arity.subsume_sols(self, valid_equations)


    def map(self, arity, depths, 
            operator=lambda *args: args,
            based_instantiation=True, 
            return_comprehensive_terms_cache=False,
            **kwds):

        # input destructuring to forward to composed functions
        first_order = kwds.get('first_order', True)

        comprehensive_terms_cache = {}

        def worker(depth):

            unfolded_evaluated_spec = self.unfold(depth, first_order)

            comprehensive_terms_cache.update(unfolded_evaluated_spec.terms_cache)

            processed_recurrence_spec = unfolded_evaluated_spec
            if based_instantiation: 
                processed_recurrence_spec = processed_recurrence_spec.instantiate(strategy=based(arity))

            return operator(processed_recurrence_spec, depth)

        mapped = map(worker, depths)

        return (mapped, comprehensive_terms_cache) if return_comprehensive_terms_cache else mapped 

class raw:

    def __init__(self, substitutions):
        self.substitutions = substitutions

    def dispatch_instantiate_on(self, target):
        return target._instantiate_by_raw(dispatcher=self)

class based:

    def __init__(self, arity):
        self.arity = arity

    def dispatch_instantiate_on(self, target):
        return target._instantiate_by_based(dispatcher=self)

class unary_indexed: 

    def __init__(self, base_index=[0]):
        self.base_index = base_index

    def subsume_sols(self, recurrence_spec, eqs):
        index, = recurrence_spec.index
        items = []
        for subscripts_eqs in eqs:
            k, v = subscripts_eqs.popitem()
            items.append(v)
        return {index:max(items)}

class doubly_indexed: 

    def __init__(self, base_index=[None, 0]):
        _, k_index = base_index
        self.base_index = [Dummy(), k_index]

    def subsume_sols(self, recurrence_spec, eqs):
        n, k = recurrence_spec.index
        dummy_sym, k_index = self.base_index
        max_k_value = max([subscripts_eqs[k] for subscripts_eqs in eqs])
        instantiated_lhs = recurrence_spec.recurrence_eq.lhs.subs(k, max_k_value)
        with bind_Mul_indexed(instantiated_lhs, recurrence_spec.indexed) as (_, (nb, kb)):
            max_n_value = max([subscripts_eqs[n].subs(dummy_sym, kb) for subscripts_eqs in eqs])
        return {n:max_n_value, k:max_k_value}

def ipython_latex_description(rec_spec, *args, **kwds):
    
    from IPython.display import Latex

    kwds['operator'] = lambda rec_spec, depth: latex(rec_spec.recurrence_eq) + r"\\"

    mapped = rec_spec.map(*args, **kwds)
    template = Template(r"""\begin{array}{c}$content\end{array}""")
    latex_src = template.substitute(content="\n".join(mapped))

    return Latex(latex_src)

#________________________________________________________________________

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













def project_recurrence_spec(recurrence_spec, **props):
    
    projected = []
    for k,v in props.items(): 
        if v and k in recurrence_spec: projected.append(recurrence_spec[k])

    return projected[0] if len(projected) == 1 else tuple(projected)





def take_sol(*args, sol_index=0):
    sols = solve(*args)
    return sols[sol_index]

def subsume_cache(recurrence_spec):
    '''
    What do I do? It seems a reduce process to eliminate redundant elements from the cache...
    For now we leave it as it is, if I found it in other place then it we'll be refactored.
    '''
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

def fix_combination(eqs, adjust, fix):
    
    def w(eq): 
        adjust_term = adjust(eq.rhs) 
        return Eq(fix(adjust_term, eq.lhs), fix(adjust_term, eq.rhs), evaluate=False)

    return map(w, eqs)







