
from sympy import *
from sympy.abc import x, n, z, t, k
from sympy.core.cache import *
from sympy.core.function import UndefinedFunction

from functools import reduce

def symbolic_matrix(dims, gen_coeff_symbol, rule, inits, lower=True):
    return Matrix(*dims, lambda n,k: 0 if lower and n < k else gen_coeff_symbol[n,k])

def make_lower_triangular(m):
    for r in range(m.rows):
        for c in range(r+1, m.cols):
            m[r,c] = 0
            
def unfold_in_matrix(m, rec, 
            unfold_row_start_index=1, unfolding_rows=None,
            unfold_col_start_index=0, row_sym=Symbol('n'), col_sym=Symbol('k'),
            include_substitutions=False):
    
    m = m.copy()
    indexed_sym, row_sym_index, col_sym_index = rec.lhs.args
    if unfolding_rows is None: unfolding_rows = m.rows

    substitutions = {}
    
    for r in range(unfold_row_start_index, unfolding_rows):
        for c in range(unfold_col_start_index, r+1):
            row_eq, col_eq = Eq(row_sym_index,r), Eq(col_sym_index,c)
            row_sol, col_sol = (solve(row_eq, row_sym)[0], solve(col_eq, col_sym)[0])
            instantiated_rec = rec.subs({row_sym: row_sol, col_sym:col_sol}, simultaneous=True)
            #instantiated_rec = rec.replace(row_sym, row_sol).replace(col_sym, col_sol)
                #.subs({row_sym: row_sol, col_sym:col_sol}, simultaneous=True)
            unfold_term = 0
            #for summand in flatten(instantiated_rec.rhs.args, cls=Add):
            for summand in instantiated_rec.rhs.args:
                coeff_wild = Wild('coeff', exclude=[indexed_sym])
                row_wild = Wild('n', exclude=[indexed_sym])
                col_wild = Wild('k', exclude=[indexed_sym])
                matched = summand.match(coeff_wild * indexed_sym[row_wild, col_wild])
                if not matched: continue
                inst_row_index = matched[row_wild]
                inst_col_index = matched[col_wild]
                coeff = matched[coeff_wild]
                if inst_row_index in range(m.rows) and inst_col_index in range(m.cols):
                    unfold_term += coeff * m[inst_row_index, inst_col_index]
            m[r,c] = unfold_term
            substitutions.update({indexed_sym[r,c] : unfold_term})

    return (m, substitutions) if include_substitutions else m
            
def build_rec_from_gf(gf_spec, indexed_sym, 
                      row_sym=Symbol('n'), col_sym=Symbol('k'), evaluate=False):
    '''I have to build a recurrence starting from `indexed_sym[n+1, k+1]`'''
    gf, gf_var, n = gf_spec
    gf_series = gf.series(gf_var, n=n)

    #rhs = 0
    #for i in range(n): rhs += gf_series.coeff(gf_var, n=i) * indexed_sym[row_sym, col_sym + i]
    summands = [gf_series.coeff(gf_var, n=i) * indexed_sym[row_sym, col_sym + i] for i in range(n)]
    rhs = Add(*summands, evaluate=False).doit(deep=False)
        
    return Eq(indexed_sym[row_sym+1, col_sym+1], rhs)
    
def apply_subs(m, substitutions):
    term = m
    for k,v in substitutions.items(): term = Subs(term.replace(k,v), k, v)
    return term

def unfold_upper_chunk(*args, **kwds):
    matrix, substitutions = unfold_in_matrix(*args, 
        unfold_row_start_index=1, unfold_col_start_index=1, 
        include_substitutions=True, **kwds)
    return matrix.subs(substitutions, simulataneous=True)

def build_rec_from_A_matrix(A_matrix): pass

def build_rec_from_A_sequence(A_sequence_spec, symbolic_row_index = Symbol('n')+1):
    A_sequence_gf, indeterminate, order = A_sequence_spec
    return build_rec_from_A_matrix({(symbolic_row_index-1) : (A_sequence, indeterminate)}, order)

def extract_inner_matrices(matrix, indexed_sym, unfolding_rows):

    matrices = {}

    for row in range(unfolding_rows):

        current_symbolic_element = indexed_sym[row, 0]

        def worker(r, c):

            if r < c: return 0 

            wild_coeff, wild_rest = Wild("coeff", exclude=[0]), Wild("rest")
            matched = matrix[r,c].match(wild_coeff*current_symbolic_element + wild_rest)
            return matched[wild_coeff] if matched else 0 

        matrices[current_symbolic_element] = Matrix(matrix.rows, matrix.cols, worker)

    return matrices

def check_matrix_expansion(m, expansion, inits={}):
    sum_matrix = zeros(m.rows, m.cols)
    for k,v in expansion.items(): sum_matrix += k * v
    return Eq(m, sum_matrix).subs(inits).simplify()

def make_abstract_A_sequence(spec, inits={}):

    indexed_sym, indeterminate, order = spec

    def getter(index):
        if isinstance(indexed_sym, IndexedBase): return indexed_sym[index]
        elif isinstance(indexed_sym, UndefinedFunction): return indexed_sym(index)
        else: raise Exception("Only `IndexedBase` or `UndefinedFunction` symbols" +
                        " are accepted to build abstract A-sequences.")

    # maybe it should be better to use list comprehension like this:
    #for i in range(order): term += indexed_sym[i]*indeterminate**i
    summands = [getter(i)*indeterminate**i for i in range(order)]
    term = Add(*summands, evaluate=False).doit(deep=False)
    
    return term.subs(inits)


















