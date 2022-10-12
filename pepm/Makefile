pepm.pdf: pepm.tex pepm.blg
	pdflatex --shell-escape pepm

pepm.aux: pepm.tex
	pdflatex --shell-escape pepm

pepm.blg: pepm.aux cites.bib
	bibtex pepm


