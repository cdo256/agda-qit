#!/usr/bin/env python3
"""
Simplified build script for single literate Agda paper.
Converts paper.lagda.md to PDF via Pandoc -> Agda -> LaTeX -> PDF pipeline.
"""

import os
import shutil
import subprocess as sp
import sys
import tempfile


def run_cmd(cmd, description):
    """Run a command and handle errors gracefully."""
    print(f"Running: {' '.join(cmd)}", file=sys.stderr)
    try:
        result = sp.run(cmd, check=True, capture_output=True, text=True)
        return result
    except sp.CalledProcessError as e:
        print(f"Error in {description}:", file=sys.stderr)
        print(f"Return code: {e.returncode}", file=sys.stderr)
        print(f"Stdout: {e.stdout}", file=sys.stderr)
        print(f"Stderr: {e.stderr}", file=sys.stderr)
        sys.exit(1)


def init_dirs():
    """Initialize required directories."""
    os.makedirs("_build", exist_ok=True)
    os.makedirs("_build/latex", exist_ok=True)


def convert_to_tex():
    """Convert .lagda.md to .lagda.tex using Pandoc."""
    cmd = [
        "pandoc",
        "-f",
        "markdown",
        "-t",
        "latex",
        "--standalone",
        "--template",
        "_build/paper-template.tex",
        "-o",
        "_build/paper.lagda.tex",
        "paper.lagda.md",
    ]
    run_cmd(cmd, "Pandoc conversion")


def process_with_agda():
    """Process .lagda.tex with Agda to generate LaTeX."""
    cmd = ["agda", "--latex-dir=_build/latex", "--latex", "_build/paper.lagda.tex"]
    run_cmd(cmd, "Agda LaTeX generation")


def compile_pdf():
    """Compile the final PDF using XeLaTeX."""
    # Copy the generated LaTeX to final location
    if os.path.exists("_build/latex/paper.tex"):
        shutil.copy("_build/latex/paper.tex", "_build/paper.tex")
    else:
        print("Error: Agda did not generate paper.tex", file=sys.stderr)
        sys.exit(1)

    # Run XeLaTeX twice for proper references
    for i in range(2):
        cmd = [
            "xelatex",
            "-interaction=nonstopmode",
            "-output-directory=_build",
            "_build/paper.tex",
        ]
        run_cmd(cmd, f"XeLaTeX compilation (pass {i + 1})")

    # Copy final PDF to root
    if os.path.exists("_build/paper.pdf"):
        shutil.copy("_build/paper.pdf", "paper.pdf")
        print("✓ Successfully generated paper.pdf")
    else:
        print("Error: PDF was not generated", file=sys.stderr)
        sys.exit(1)


def create_latex_template():
    """Create a minimal LaTeX template for the paper."""
    template_content = r"""
\documentclass[11pt,a4paper]{article}
\usepackage{amsmath,amssymb,amsthm}
\usepackage{fontspec}
\usepackage{unicode-math}
\usepackage{hyperref}
\usepackage{tikz-cd}
\usepackage[references]{latex/agda}

% Font setup
\setmainfont{DejaVu Serif}
\setmonofont{JuliaMono}

% Agda code style
\renewcommand{\AgdaCodeStyle}{%
    \footnotesize
    \setmonofont{JuliaMono}
}

% Theorem environments
\newtheorem{theorem}{Theorem}
\newtheorem{lemma}{Lemma}
\theoremstyle{definition}
\newtheorem{definition}{Definition}

$if(title)$
\title{$title$}
$endif$
$if(author)$
\author{$author$}
$endif$
$if(date)$
\date{$date$}
$else$
\date{\today}
$endif$

\begin{document}

$if(title)$
\maketitle
$endif$

$if(toc)$
\tableofcontents
\newpage
$endif$

$body$

\end{document}
"""
    with open("_build/paper-template.tex", "w") as f:
        f.write(template_content)


def main():
    """Main build pipeline."""
    if not os.path.exists("paper.lagda.md"):
        print("Error: paper.lagda.md not found", file=sys.stderr)
        sys.exit(1)

    print("Building literate Agda paper...")

    init_dirs()
    create_latex_template()
    convert_to_tex()
    process_with_agda()
    compile_pdf()

    print("Build completed successfully!")


if __name__ == "__main__":
    main()
