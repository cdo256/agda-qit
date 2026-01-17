OUT := out/latex
export BIBINPUTS := latex:

.PHONY: all clean

all: construction abstract

construction: latex/construction.tex
	latexmk -pdf -output-directory=$(OUT) -interaction=nonstopmode $<

abstract: latex/types2026/abstract.tex
	latexmk -pdf -output-directory=$(OUT)/types2026 -interaction=nonstopmode $<

build:
	agda Everything.agda

clean:
	rm -rf out
