
# Recurrences unfolding

This project aims to implement a prototype to unfold recurrence
relations *symbolically*. Our definitions are built on top of *SymPy*
and target Python **3.5.1**.

We describe prototype features in a [notebook][recurrences-unfolding], 
where some unfolded recurrences are shown. We split the content 
about the underlying *Binomial transform*, which arises
in the characterization of Fibonacci numbers with odd subscripts, 
in a [companion document][companion].

# Colouring matrices

We provide a set of simple functions to colour a matrice where coefficients
are taken according a congruence relation. Such functions, in addition to
the colouring features, allows to build the Catalan triangle modularly,
using theorems proved in my master thesis. A simple notebook showing an
application to Catalan Riordan array can be seen [here][catalan-modular].

# A basic introduction to SymPy

Moreover, we provide a Jupyter notebook to support a lecture within the course
*Progettazione e Analisi degli Algoritmi* (PAA for short) taught
by professors [Merlini] and [Verri] at the University of Florence. The [notebook][here]
present a basic introduction to [SymPy] for students.

[Verri]:http://www.dsi.unifi.it/~cecilia/
[Merlini]:http://local.disia.unifi.it/merlini/
[here]:http://nbviewer.jupyter.org/github/massimo-nocentini/recurrences-unfolding/blob/master/paa-course/an-introduction-to-sympy.ipynb?flush_cache=true
[SymPy]:http://www.sympy.org/en/index.html
[recurrences-unfolding]:http://nbviewer.jupyter.org/github/massimo-nocentini/recurrences-unfolding/blob/master/sympy-notebook/recurrences-unfolding.ipynb?flush_cache=true
[companion]:http://nbviewer.jupyter.org/github/massimo-nocentini/recurrences-unfolding/blob/master/sympy-notebook/binomial-transform-applied-to-fibonacci-numbers.ipynb?flush_cache=true
[catalan-modular]:http://nbviewer.jupyter.org/github/massimo-nocentini/recurrences-unfolding/blob/master/sympy-notebook/colouring-matrices.ipynb?flush_cache=true
