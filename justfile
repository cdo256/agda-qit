build:
  ./build.py

paper:
  ./build-paper.py

clean:
  git clean -X -fd

clean-paper:
  rm -rf _build paper.pdf
