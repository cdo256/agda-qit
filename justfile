build:
  ./build.py

paper:
  ./build-paper.py

paper-fast:
  ./build-paper.py --no-typecheck

clean:
  git clean -X -fd

clean-paper:
  rm -rf _build paper.pdf
