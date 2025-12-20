#!/usr/bin/env python3
import re
import os
import sys
import glob
import subprocess as sp

SRC_DIR = "./src/Dissertation"
LATEX_DIR = "./latex"
PDF_OUT_FILE = "./dissertation.pdf"


def init():
    os.makedirs(LATEX_DIR, exist_ok=True)
    os.makedirs("./src/DissertationTex", exist_ok=True)
    os.makedirs("./latex/generated/DissertationTex", exist_ok=True)
    os.makedirs("./out", exist_ok=True)


def replace_verbatim_with_code(filename):
    print("Replacing verbatim with code", file=sys.stderr)
    with open(filename, "r", encoding="utf-8") as f:
        content = f.read()
    new_content = content.replace("{verbatim}", "{code}")
    with open(filename, "w", encoding="utf-8") as f:
        f.write(new_content)


def build_tex():
    input_files = glob.glob(os.path.join(SRC_DIR, "*.lagda.md"))
    if not input_files:
        raise FileNotFoundError(f"No .lagda.md files found in {SRC_DIR}")
    for infile in input_files:
        base = os.path.splitext(os.path.splitext(os.path.basename(infile))[0])[0]
        outfile = os.path.join("./src/DissertationTex", base + ".lagda.tex")
        cmd = ["pandoc", "-o", outfile, infile]
        print("Running:", " ".join(cmd), file=sys.stderr)
        sp.run(cmd, check=True)
        replace_verbatim_with_code(outfile)
        cmd = ["agda", "--latex-dir=./latex/generated", "--latex", outfile]
        print("Running:", " ".join(cmd), file=sys.stderr)
        sp.run(cmd, check=True)


def build_pdf():
    cmd = [
        "xelatex",
        "--interaction=nonstopmode",
        "--file-line-error",
        "--jobname=dissertation",
        "./latex/main.tex",
    ]
    print("Running:", " ".join(cmd), file=sys.stderr)
    proc = sp.run(cmd, stdout=sp.PIPE, stderr=sp.PIPE, text=True)
    if proc.returncode != 0:
        print("PDF Build failed :(")
        exit(1)


if __name__ == "__main__":
    init()
    build_tex()
    build_pdf()
