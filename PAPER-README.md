# Simplified Literate Agda Paper Workflow

This directory contains a simplified build system for writing academic papers with embedded literate Agda code. It's designed for single-paper workflows, in contrast to the more complex dissertation setup in the main build system.

## Quick Start

1. Edit your paper content in `Paper.lagda.md`
2. Run `just paper-fast` for quick builds during writing
3. Run `just paper` for final builds with full type checking

## Files

- **`Paper.lagda.md`** - Your main paper file (literate Agda with Markdown)
- **`build-paper.py`** - Simplified build script  
- **`paper.pdf`** - Generated output
- **`_build/`** - Temporary build files (can be cleaned)

## Build Commands

### Fast Build (Recommended for drafting)
```bash
just paper-fast
# OR
./build-paper.py --no-typecheck
```

**What it does:**
- ✅ Syntax highlighting, scope resolution, LaTeX generation
- ❌ Skips type checking, totality checking, termination checking  
- ⚡ Much faster build times

### Full Build (For final versions)
```bash
just paper
# OR  
./build-paper.py
```

**What it does:**
- ✅ Complete Agda verification including type checking
- 🐌 Slower but ensures correctness

### Clean Build Files
```bash
just clean-paper
# OR
rm -rf _build paper.pdf
```

## How It Works

The build pipeline is:

1. **Copy**: `Paper.lagda.md` → `BuildPaper.lagda.md` (temporary, for Agda module path requirements)
2. **Agda**: Processes literate Agda to generate LaTeX with syntax highlighting
3. **LaTeX**: Compiles to PDF using XeLaTeX with proper fonts and math support
4. **Cleanup**: Removes temporary files

## Writing Literate Agda

Your `Paper.lagda.md` should contain:

- Standard Markdown for prose (headings, paragraphs, math)
- Agda code in fenced code blocks:

````markdown
## Section Title

Some mathematical discussion about setoids...

```agda
record Setoid ℓ : Set (lsuc ℓ) where
  field
    Carrier : Set ℓ
    _≈_ : Carrier → Carrier → Set ℓ
    isEquivRel : IsEquivalence _≈_
```

More discussion...
````

## Features

- **Single file workflow** - everything in one `Paper.lagda.md`
- **Fast iteration** - `--no-typecheck` for quick preview builds
- **Proper typography** - Unicode math, professional fonts (DejaVu Serif, JuliaMono)
- **Agda integration** - Syntax-highlighted code with LaTeX quality
- **Self-contained** - minimal dependencies, clear build process

## Dependencies

All dependencies are provided by the Nix development shell:

```bash
nix develop  # Enter development environment
```

This provides: Agda, XeLaTeX, Python, fonts, and all required packages.

## Comparison to Main Build System

| Feature | Main System | Paper System |
|---------|-------------|-------------|
| **Scope** | Multi-chapter dissertation | Single paper |
| **Complexity** | Complex LaTeX structure | Simple article format |
| **Files** | Multiple `.lagda.md` files | One `Paper.lagda.md` file |
| **Build time** | Longer | Much faster |
| **Use case** | Thesis/dissertation | Conference/journal papers |

## Tips

- Use `just paper-fast` during writing for quick feedback
- Use `just paper` before submission to ensure everything type-checks
- The paper compiles to a clean, professional-looking PDF suitable for submission
- Agda code gets proper syntax highlighting and mathematical typography
- All holes `{!!}` are clearly marked in the output

## Troubleshooting

**"Module name doesn't match filename"**: This is handled automatically by the build script, which creates a temporary `BuildPaper.lagda.md` file.

**LaTeX warnings**: The build script tolerates common LaTeX warnings as long as a PDF is generated successfully.

**Type checking errors**: Use `just paper-fast` to generate output even with type errors, then fix them before the final build.

**Fonts missing**: Make sure you're in the Nix development shell (`nix develop`).