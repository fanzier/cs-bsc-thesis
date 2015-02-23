lhsfiles = commands.lhs 1-introduction.lhs 2-preliminaries.lhs 3-operational.lhs 4-translation.lhs 5-analysis.lhs 6-conclusion.lhs thesis.lhs
miscfiles = format.fmt thesis.bib
builddir = build

default: thesis.pdf

thesis.pdf: $(builddir) $(miscfiles) $(lhsfiles) $(texfiles)
	lhs2TeX thesis.lhs -o thesis.tex
	latexmk -interaction=nonstopmode -pdf -jobname=$(builddir)/thesis thesis
	cp $(builddir)/thesis.pdf thesis.pdf

$(builddir):
	mkdir -p $(builddir)

.PHONY clean :
	rm -rf build
