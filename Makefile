OUT := out/latex
export BIBINPUTS := latex:
export TEXINPUTS := latex:

# Find all .tex files in latex directory, excluding preambles
TEX_FILES := $(filter-out latex/preamble.tex,$(wildcard latex/*.tex))
PDF_FILES := $(patsubst latex/%.tex,$(OUT)/%.pdf,$(TEX_FILES))
BIB_FILES := latex/master.bib

.PHONY: all clean build pdf

all: pdf build

pdf: $(PDF_FILES)

$(OUT)/%.pdf: latex/%.tex $(BIB_FILES)
	@mkdir -p $(OUT)
	latexmk -pdf -output-directory=$(OUT) -interaction=nonstopmode $<

build:
	agda Everything.agda

clean:
	rm -rf out
