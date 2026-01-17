# Agda QIT Project Makefile

# Directories
OUT_DIR := out
LATEX_DIR := latex
TYPES2026_DIR := $(LATEX_DIR)/types2026

# Output files
CONSTRUCTION_PDF := $(OUT_DIR)/construction.pdf
ABSTRACT_PDF := $(OUT_DIR)/types2026/abstract.pdf

# Source files
CONSTRUCTION_TEX := $(LATEX_DIR)/construction.tex
ABSTRACT_TEX := $(TYPES2026_DIR)/abstract.tex
BIBLIOGRAPHY := $(LATEX_DIR)/master.bib

.PHONY: all pdf pdf-construction pdf-abstract build clean clean-pdf help

# Default target
all: pdf

# Build Agda project
build:
	agda Everything.agda

# Compile all PDFs
pdf: $(CONSTRUCTION_PDF) $(ABSTRACT_PDF)

# Individual PDF targets
pdf-construction: $(CONSTRUCTION_PDF)
pdf-abstract: $(ABSTRACT_PDF)

# Construction paper compilation
$(CONSTRUCTION_PDF): $(CONSTRUCTION_TEX) $(BIBLIOGRAPHY)
	@mkdir -p $(OUT_DIR)
	@cp $(BIBLIOGRAPHY) $(OUT_DIR)/
	latexmk -pdf -output-directory=$(OUT_DIR) \
		-interaction=nonstopmode -f $(CONSTRUCTION_TEX)

# Abstract paper compilation
$(ABSTRACT_PDF): $(ABSTRACT_TEX) $(BIBLIOGRAPHY)
	@mkdir -p $(OUT_DIR)/types2026
	@cp $(BIBLIOGRAPHY) $(OUT_DIR)/types2026/
	latexmk -pdf -output-directory=$(OUT_DIR)/types2026 \
		-interaction=nonstopmode -f $(ABSTRACT_TEX)

# Clean targets
clean:
	git clean -X -fd

clean-pdf:
	rm -rf $(OUT_DIR)
	latexmk -c $(CONSTRUCTION_TEX) $(ABSTRACT_TEX)

clean-all: clean clean-pdf

# Help target
help:
	@echo "Available targets:"
	@echo "  all           - Build all PDFs (default)"
	@echo "  pdf           - Build all PDFs"
	@echo "  pdf-construction - Build construction.pdf only"
	@echo "  pdf-abstract  - Build abstract.pdf only"
	@echo "  build         - Build Agda project"
	@echo "  clean         - Clean git-ignored files"
	@echo "  clean-pdf     - Clean PDF outputs and LaTeX auxiliary files"
	@echo "  clean-all     - Clean everything"
	@echo "  help          - Show this help"
