npj.pdf: npj.tex npj.blg
	pdflatex --shell-escape npj

npj.aux: npj.tex
	pdflatex --shell-escape npj

npj.blg: npj.aux cites.bib
	bibtex npj


