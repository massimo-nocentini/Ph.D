
pdf:
	lualatex --shell-escape on-recurrences-unfolding.tex

bibtex-and-references:
	pdflatex --shell-escape on-recurrences-unfolding.tex
	bibtex on-recurrences-unfolding
	pdflatex --shell-escape on-recurrences-unfolding.tex
	pdflatex --shell-escape on-recurrences-unfolding.tex

complete: pascal-explanations bibtex-and-references
