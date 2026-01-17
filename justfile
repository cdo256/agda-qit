build:
  agda Everything.agda

clean:
  git clean -X -fd

clean-paper:
  rm -rf _build paper.pdf
