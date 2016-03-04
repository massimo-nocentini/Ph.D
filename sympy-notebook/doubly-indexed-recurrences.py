
from sympy import *
from sympy.abc import x, n, z, t, k
from sympy.core.cache import *
from sympy.core.function import UndefinedFunction
from sympy.printing.latex import latex

import re

from functools import reduce

class AbstractGenericElement(object): 

    def accept(self, visitor): pass


class IndexedBaseGenericElement(AbstractGenericElement): 

    def __init__(self, indexed_base):
        self.indexed_base = indexed_base

    def accept(self, visitor): return visitor.forIndexedBaseGenericElement(self)

    def __getitem__(self, indexes): return self.indexed_base[indexes] 
        

class UndefinedFunctionGenericElement(AbstractGenericElement):

    def __init__(self, undefined_function):
        self.undefined_function = undefined_function

    def accept(self, visitor): return visitor.forUndefinedFunctionGenericElement(self)

    def __call__(self, *args): return self.undefined_function(*args)


class IndexingGenericElementVisitor:
    
    def __init__(self, ge): 
        self.ge = ge

    def __call__(self, *indexes):
        self.indexes = indexes
        return self.ge.accept(self)

    def forIndexedBaseGenericElement(self, ibge): return ibge[self.indexes]

    def forUndefinedFunctionGenericElement(self, ufge): return ufge(*self.indexes) 


def make_generic_element(generic_term):

    if isinstance(generic_term, IndexedBase): 
        return IndexedBaseGenericElement(generic_term)
    elif isinstance(generic_term, UndefinedFunction): 
        return UndefinedFunctionGenericElement(generic_term)
    
    raise Exception("Only `IndexedBase` or `UndefinedFunction` symbols" +
                    " are accepted to build abstract A-sequences.")

def symbolic_matrix(dims, gen_coeff_symbol, inits={}, 
                    lower=True, return_full_matrix_spec=True):

    ge = make_generic_element(gen_coeff_symbol)
    indexer = IndexingGenericElementVisitor(ge)
    m = Matrix(*dims, lambda n,k: 0 if lower and n < k else indexer(n,k))
    for sym_coeff, v in inits.items(): m = Subs(m.subs(sym_coeff, v), sym_coeff, v)
    return (m, gen_coeff_symbol) if return_full_matrix_spec else m

def make_lower_triangular(m_spec):
    m, generic_sym = m_spec
    m = m.copy()
    for r in range(m.rows):
        for c in range(r+1, m.cols):
            m[r,c] = 0
    return m, generic_sym
            
class AbstractSequence:

    def __init__(self, rec):
        self.rec = rec
        self.other_seq = None

    def tie_other_seq(self, other_seq): self.other_seq = other_seq

    def nextone(self): pass

    def instantiate(self, r, c): pass


class Zsequence(AbstractSequence):
    
    def __getitem__(self, col): return self.rec if col is 0 else self.other_seq[col]

    def nextone(self): return self.other_seq

    def instantiate(self, row, col):
        
        row_sym, r = row
        col_sym, c = col
        indexed_sym, row_sym_index, col_sym_index = self.rec.lhs.args

        assert c == 0 and col_sym_index == 0, "c:{0}, col:{1}".format(c, col_sym_index)

        row_eq = Eq(row_sym_index,r)
        row_sol = solve(row_eq, row_sym)[0]
        return self.rec.subs(row_sym, row_sol)


class Asequence(AbstractSequence): 

    def __getitem__(self, col): return self.rec if col > 0 else self.other_seq[col]

    def nextone(self): return self

    def instantiate(self, row, col):
        
        row_sym, r = row
        col_sym, c = col
        indexed_sym, row_sym_index, col_sym_index = self.rec.lhs.args

        row_eq, col_eq = Eq(row_sym_index,r), Eq(col_sym_index,c)
        row_sol, col_sol = (solve(row_eq, row_sym)[0], solve(col_eq, col_sym)[0])
        return self.rec.subs({row_sym: row_sol, col_sym:col_sol}, simultaneous=True)

def explode_term_respect_to(term, op_class, deep=False):

    exploded = None
    if isinstance(term, op_class): 
        exploded = flatten(term.args, cls=op_class) if deep else term.args
    else: exploded = [term]

    return exploded
    

def unfold_in_matrix(m_spec, Arec, Zrec=None,
            unfold_row_start_index=1, unfolding_rows=None, unfolding_cols=None,
            unfold_col_start_index=0, row_sym=Symbol('n'), col_sym=Symbol('k'),
            include_substitutions=False):

    m, indexed_sym = m_spec
    m = m.copy()

    Aseq = Asequence(Arec)

    Zseq = Aseq if Zrec is None else Zsequence(Zrec)

    if unfolding_rows is None: unfolding_rows = m.rows

    substitutions = {}
    variables = free_variables_in_matrix(m_spec, unfolding_rows)
    
    for r in range(unfold_row_start_index, unfolding_rows):
        
        sequence = Aseq if unfold_col_start_index > 0 else Zseq
        
        cols = r+1 if unfolding_cols is None else unfolding_cols
        for c in range(unfold_col_start_index, cols):

            instantiated_rec = sequence.instantiate((row_sym, r), (col_sym, c))

            unfold_term = 0

            for summand in explode_term_respect_to(instantiated_rec.rhs, Add):
                coeff_wild = Wild('coeff', exclude=[indexed_sym])
                row_wild = Wild('n', exclude=[indexed_sym])
                col_wild = Wild('k', exclude=[indexed_sym])
                matched = summand.match(coeff_wild * indexed_sym[row_wild, col_wild])
                if not matched or coeff_wild not in matched or row_wild not in matched or col_wild not in matched: continue
                inst_row_index = matched[row_wild]
                inst_col_index = matched[col_wild]
                coeff = matched[coeff_wild]
                if inst_row_index in range(m.rows) and inst_col_index in range(m.cols):
                    unfold_term = unfold_term + coeff * m[inst_row_index, inst_col_index]

            unfold_term = Poly(unfold_term, variables).args[0]
            m[r,c] = unfold_term
            substitutions.update({indexed_sym[r,c] : unfold_term})

            sequence = Aseq

    m_spec = m, indexed_sym
    return (m_spec, substitutions) if include_substitutions else m_spec
            
def build_rec_from_gf(gf_spec, indexed_sym, 
                      row_sym=Symbol('n'), col_sym=Symbol('k'), evaluate=False):

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

    matrix_spec, substitutions = unfold_in_matrix(*args, 
        unfold_row_start_index=1, unfold_col_start_index=1, 
        include_substitutions=True, **kwds)

    matrix, indexed_sym = matrix_spec

    subs_matrix = matrix.subs(substitutions, simulataneous=True).applyfunc(
        lambda term: Poly(term, free_variables_in_matrix(matrix_spec, kwds['unfolding_rows'])).args[0])

    return subs_matrix, indexed_sym

def entail_dependencies(matrix_spec, unfolding_rows):

    matrix, indexed_sym = matrix_spec

    return {indexed_sym[r,0]:matrix[r,0] for r in range(1, unfolding_rows)}

def build_rec_from_A_matrix(A_matrix): pass

def build_rec_from_A_sequence(A_sequence_spec, symbolic_row_index = Symbol('n')+1):
    A_sequence_gf, indeterminate, order = A_sequence_spec
    return build_rec_from_A_matrix({(symbolic_row_index-1) : (A_sequence, indeterminate)}, order)

def extract_inner_matrices(m_spec, unfolding_rows):

    matrix, indexed_sym = m_spec

    matrices = {}

    variables = free_variables_in_matrix(m_spec, unfolding_rows)

    for row in range(unfolding_rows):

        current_symbolic_element = indexed_sym[row, 0]
        nullable_variables = variables - set([current_symbolic_element])
        substitutions = {var:0 for var in nullable_variables}

        nullable_matrix = matrix.subs(substitutions, simultaneous=True)

        def worker(r, c):

            if r < c: return 0 

            wild_coeff = Wild("coeff")
            matched = nullable_matrix[r,c].match(wild_coeff*current_symbolic_element)

            #if not matched or wild_coeff not in matched: print("r:{} c:{} not matched: {}".format(r,c,nullable_matrix[r,c]))
            #if r==5 and c==1: print("5 1: {}".format(matched[wild_coeff]))
            #if matched[wild_coeff] == 0: print("r:{} c:{} has 0 for {}".format(r,c,current_symbolic_element))
            return matched[wild_coeff] if matched and wild_coeff in matched else 0

        matrices[current_symbolic_element] = Matrix(matrix.rows, matrix.cols, worker)

    return matrices

def check_matrix_expansion(m_spec, expansion, inits={}, perform_asserts=True):

    m, indexed_sym = m_spec

    sum_matrix = zeros(m.rows, m.cols)

    for k,v in expansion.items(): sum_matrix = sum_matrix + (k * v)

    sum_matrix = sum_matrix.subs(inits, simultaneous=True).applyfunc(
        lambda term: Poly(term, indexed_sym[0,0]).args[0])

    eq = Eq(m, sum_matrix)
    
    if eq == True: return True

    for r in range(m.rows):
        for c in range(r+1):
            v1 = eq.lhs[r, c].expand()
            v2 = eq.rhs[r, c].expand()
            if not (v1 == v2): 
                if perform_asserts: assert False, "Row: {} Col: {} --- {} != {}".format(r, c, v1, v2)
                else: return False

    return True

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


def factorize_matrix_as_matrices_sum(matrix_spec, length=None, perform_check=False, *args, **kwds):
    
    matrix = matrix_spec[0]
    if length is None: length = matrix.rows

    assert length <= matrix.rows, "It was required an expansion using {} matrices when" + \
        " the provided matrix had {} rows".format(length, matrix_spec[0].rows)

    unfolded_matrix_spec = unfold_in_matrix(matrix_spec, *args, **kwds)
    splitted_matrix_spec = unfold_in_matrix(matrix_spec, *args, unfold_row_start_index=length, **kwds)
    clean_splitted_matrix_spec = unfold_upper_chunk(splitted_matrix_spec, *args, unfolding_rows=length, **kwds)
    matrix_expansion = extract_inner_matrices(clean_splitted_matrix_spec, unfolding_rows=length)
    inits_dependencies = entail_dependencies(unfolded_matrix_spec, unfolding_rows=length)

    if perform_check:
        should_be_true = check_matrix_expansion(unfolded_matrix_spec, matrix_expansion, inits_dependencies)
        assert should_be_true == True

    return dict(unfolded=extract_inner_matrices(unfolded_matrix_spec, unfolding_rows=1), 
                splitted=clean_splitted_matrix_spec[0],
                expansion=matrix_expansion,
                dependencies=inits_dependencies,
                generic_symbol=unfolded_matrix_spec[1])

def instantiate_factorization(factorization, inits=None, perform_check=False):
    
    gen_sym = factorization['generic_symbol']

    if inits is None: inits = {gen_sym[0,0]:1}

    dependencies = {k:v.subs(inits) for k,v in factorization['dependencies'].items()}
    splitted = factorization['splitted'].subs(dependencies).subs(inits).applyfunc(lambda term: expand(term))
    inst_factorization = dict(  unfolded={k.subs(inits):v for k,v in factorization['unfolded'].items()},
                                splitted=splitted,
                                expansion=[(k.subs(dependencies), v) for k,v in factorization['expansion'].items()],
                                dependencies=dependencies,
                                generic_symbol=factorization['generic_symbol'])

    if perform_check:
        for k,v in inst_factorization['unfolded'].items():
            checking_matrix = k*v
            for r in range(v.rows):
                for c in range(v.cols):
                    v1 = checking_matrix[r,c].expand()
                    v2 = inst_factorization['splitted'][r, c]
                    assert v1 == v2, "Row: {} Col: {} --- {} != {}".format(r, c, v1, v2)

    return inst_factorization

def apply_factor_inside_matrix(matrix_spec, inits=None):
    
    gen_sym = matrix_spec[1]

    if inits is None: inits = {gen_sym[0,0]:1}

    return matrix_spec[0].subs(inits).applyfunc(lambda term: factor(term)), gen_sym


def free_variables_in_matrix(matrix_spec, unfolding_rows):
    
    matrix, indexed_sym = matrix_spec
    return set(matrix[r,0] for r in range(unfolding_rows))
    #variables = set()
    #for r in range(unfolding_rows):
        #variables.add(indexed_sym[r,0])
        ##for c in range(r+1):
            ##variables.add(matrix[r,c])
    #return variables

def clean_up_zeros(matrix_spec, label="", colors={}, environment="equation", cancel_zeros=True):
    matrix, indexed_sym = matrix_spec
    #tex_code = latex(matrix, mode="equation")
    #p = re.compile(r'\begin{matrix}')
    #tex_code = p.sub(r'\begin{matrix}'+"\n", tex_code)
    #p = re.compile(r'\end{matrix}')
    #tex_code = p.sub("\n"+r'\end{matrix}', tex_code)
    #p = re.compile(r'\\')
    #tex_code = p.sub(r'\\'+"\n", tex_code)
    #p = re.compile(r'& 0 &')
    #tex_code = p.sub( '&   &', tex_code)
    tex_code = r"\begin{" + environment + r"}" + "\n" if environment else ""
    tex_code += r"\left[\begin{matrix}" + "\n"
    for r in range(matrix.rows):
        for c in range(matrix.cols):
            space = "\t" if c == 0 else " "

            if r < c: coeff_str = ""
            elif cancel_zeros: coeff_str = latex(matrix[r,c]) if matrix[r,c] != 0 else ""
            else: coeff_str = latex(matrix[r,c])

            if (r,c) in colors: coeff_str = r'\textcolor{' + colors[(r,c)] + r'}{' + coeff_str + "}"
            tex_code += "{}{} {}".format(space, coeff_str, r'\\' if c == matrix.cols-1 else r'&') 

        tex_code += "" if r == matrix.rows - 1 else "\n"

    label = "\n{}".format(r'\label{eq:' + label + r'}' + "\n" if label else "")
    tex_code += "\n" + r'\end{matrix}\right]' 
    tex_code += label + r'\end{' + environment + '}' if environment else ""

    return tex_code

def latex_of_matrix_expansion(matrix_expansion, *args, **kwds):
    tex_code = ""
    add_code = " + "
    for k,v in matrix_expansion.items():
        tex_code += latex(k) + clean_up_zeros((v, None), *args, environment=None, **kwds)
        tex_code += add_code
    return tex_code[0:-len(add_code)]

