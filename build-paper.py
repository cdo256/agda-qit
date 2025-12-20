#!/usr/bin/env python3
import argparse
import glob
import os
import subprocess as sp
import sys

SRC_DIR = "./src/Paper"
LATEX_DIR = "./latex"
PDF_OUT_FILE = "./paper.pdf"


def init():
    os.makedirs(LATEX_DIR, exist_ok=True)
    os.makedirs("./src/PaperTex", exist_ok=True)
    os.makedirs("./latex/generated/PaperTex", exist_ok=True)
    os.makedirs("./out", exist_ok=True)


def replace_verbatim_with_code(filename):
    print("Replacing verbatim with code", file=sys.stderr)
    with open(filename, "r", encoding="utf-8") as f:
        content = f.read()
    new_content = content.replace("{verbatim}", "{code}")
    with open(filename, "w", encoding="utf-8") as f:
        f.write(new_content)


def change_module_name(filename, old_name, new_name):
    """Change module name in the generated file to match path structure."""
    print(f"Changing module from {old_name} to {new_name}", file=sys.stderr)
    with open(filename, "r", encoding="utf-8") as f:
        content = f.read()
    new_content = content.replace(
        f"module {old_name} where", f"module {new_name} where"
    )
    with open(filename, "w", encoding="utf-8") as f:
        f.write(new_content)


def build_tex(no_typecheck=False):
    input_files = glob.glob(os.path.join(SRC_DIR, "*.lagda.md"))
    if not input_files:
        raise FileNotFoundError(f"No .lagda.md files found in {SRC_DIR}")
    for infile in input_files:
        base = os.path.splitext(os.path.splitext(os.path.basename(infile))[0])[0]
        outfile = os.path.join("./src/PaperTex", base + ".lagda.tex")
        cmd = ["pandoc", "--no-highlight", "-o", outfile, infile]
        print("Running:", " ".join(cmd), file=sys.stderr)
        sp.run(cmd, check=True)
        replace_verbatim_with_code(outfile)
        # Change module name to match expected path structure
        change_module_name(outfile, "Paper", "PaperTex.Paper")

        # Copy to expected location for Agda module resolution
        import shutil

        expected_file = os.path.join("PaperTex", base + ".lagda.tex")
        os.makedirs("PaperTex", exist_ok=True)
        shutil.copy(outfile, expected_file)

        cmd = ["agda", "--latex-dir=./latex/generated", "--latex"]
        if no_typecheck:
            cmd.append("--only-scope-checking")
            print(
                "Note: Type checking disabled, only scope checking will be performed",
                file=sys.stderr,
            )
        cmd.append(expected_file)

        print("Running:", " ".join(cmd), file=sys.stderr)
        sp.run(cmd, check=True)

        # Clean up temporary file
        if os.path.exists(expected_file):
            os.remove(expected_file)


def build_pdf():
    cmd = [
        "xelatex",
        "--interaction=nonstopmode",
        "--file-line-error",
        "--jobname=paper",
        "./latex/main.tex",
    ]
    print("Running:", " ".join(cmd), file=sys.stderr)
    proc = sp.run(cmd, stdout=sp.PIPE, stderr=sp.PIPE, text=True)
    if proc.returncode != 0:
        print("PDF Build failed :(")
        exit(1)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Build literate Agda paper to PDF")
    parser.add_argument(
        "--no-typecheck",
        action="store_true",
        help="Disable Agda type checking (only perform scope checking)",
    )

    args = parser.parse_args()

    if args.no_typecheck:
        print("Mode: Fast build (no type checking)")
    else:
        print("Mode: Full build (with type checking)")

    init()
    build_tex(no_typecheck=args.no_typecheck)
    build_pdf()
