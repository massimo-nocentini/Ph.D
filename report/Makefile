
TEX_COMPILER = lualatex

DOCUMENT_NAME = on-recurrences-unfolding
DOCUMENT_NAME_TEX = $(DOCUMENT_NAME).tex

pdf:
	$(TEX_COMPILER) --shell-escape $(DOCUMENT_NAME_TEX)

bibtex-and-references:
	$(TEX_COMPILER) --shell-escape $(DOCUMENT_NAME_TEX)
	bibtex $(DOCUMENT_NAME)
	$(TEX_COMPILER) --shell-escape $(DOCUMENT_NAME_TEX)
	$(TEX_COMPILER) --shell-escape $(DOCUMENT_NAME_TEX)

clear:
	rm -rf _minted-$(DOCUMENT_NAME)/
	rm $(DOCUMENT_NAME).aux
	rm $(DOCUMENT_NAME).log
	rm $(DOCUMENT_NAME).out
	rm $(DOCUMENT_NAME).pdf
	rm $(DOCUMENT_NAME).toc

