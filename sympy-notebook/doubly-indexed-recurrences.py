
from sympy import *
from sympy.abc import x, n, z, t, k
from sympy.core.cache import *

def symbolic_matrix(dims, gen_coeff_symbol, rule, inits, lower=True):
    return Matrix(*dims, lambda n,k: 0 if lower and n < k else gen_coeff_symbol[n,k])

def make_lower_triangular(m):
    for r in range(m.rows):
        for c in range(r+1, m.cols):
            m[r,c] = 0
            
def unfold_in_matrix(m, rec, unfold_row_start_index=1, 
                     unfold_col_start_index=0, row_sym=Symbol('n'), col_sym=Symbol('k')):
    
    m = m.copy()
    indexed_sym, row_sym_index, col_sym_index = rec.lhs.args
    
    for r in range(unfold_row_start_index,m.rows):
        for c in range(unfold_col_start_index, r+1):
            row_eq, col_eq = Eq(row_sym_index,r), Eq(col_sym_index,c)
            row_sol, col_sol = (solve(row_eq, row_sym)[0], solve(col_eq, col_sym)[0])
            instantiated_rec = rec.subs({row_sym: row_sol, col_sym:col_sol}, simultaneous=True)
            unfold_term = 0
            for summand in flatten(instantiated_rec.rhs.args, cls=Add):
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
    return m
            
def build_rec_from_gf(gf_spec, indexed_sym, 
                      row_sym=Symbol('n'), col_sym=Symbol('k')):
    '''I have to build a recurrence starting from `indexed_sym[n+1, k+1]`'''
    gf, gf_var, n = gf_spec
    gf_series = gf.series(gf_var, n=n)
    rhs = 0
    for i in range(n):
        rhs += gf_series.coeff(gf_var, n=i) * indexed_sym[row_sym, col_sym + i]
        
    return Eq(indexed_sym[row_sym+1, col_sym+1], rhs)
    
def apply_subs(m, substitutions):
    #term = m.subs(substitutions)
    term = m
    for k,v in substitutions.items(): term = Subs(term.replace(k,v), k, v)
    return term
