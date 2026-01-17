OUT := out/latex
export BIBINPUTS := latex:

# Find all .tex files in latex directory, excluding preambles
TEX_FILES := $(filter-out latex/preamble.tex,$(wildcard latex/*.tex))
PDF_FILES := $(patsubst latex/%.tex,$(OUT)/%.pdf,$(TEX_FILES))

.PHONY: all clean build

all: $(PDF_FILES)

$(OUT)/%.pdf: latex/%.tex
	@mkdir -p $(OUT)
	latexmk -pdf -output-directory=$(OUT) -interaction=nonstopmode $<

build:
	agda Everything.agda

clean:
	rm -rf out
