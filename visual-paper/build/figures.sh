#!/bin/sh
# Makes figures/<label>.png from the TikZ figures of the paper source (pdflatex and Ghostscript).
# Usage, from visual-paper-v2/:  sh build/figures.sh
set -e
TEX=../paper/Homogenization_beyond_convex_growthV1.tex
[ -f "$TEX" ] || TEX=../paper-public/Homogenization_beyond_convex_growthV1.tex
OUT=figures
TMP=$(mktemp -d)
mkdir -p "$OUT"
python3 -I - "$TEX" "$TMP" <<'PY'
import re, sys, os
s = open(sys.argv[1], encoding="utf-8").read()
for m in re.finditer(r"\\begin\{figure\}.*?\\end\{figure\}", s, re.S):
    env = m.group(0)
    lab = re.search(r"\\label\{([^}]*)\}", env)
    pic = re.search(r"\\begin\{tikzpicture\}.*?\\end\{tikzpicture\}", env, re.S)
    if not (lab and pic):
        continue
    name = re.sub(r"[^A-Za-z0-9]+", "-", lab.group(1))
    with open(os.path.join(sys.argv[2], name + ".tex"), "w") as f:
        f.write("\\documentclass[border=4pt]{standalone}\n\\usepackage{amsmath,amssymb,tikz}\n"
                "\\begin{document}\n" + pic.group(0) + "\n\\end{document}\n")
PY
for f in "$TMP"/*.tex; do
  n=$(basename "$f" .tex)
  (cd "$TMP" && pdflatex -interaction=nonstopmode "$n.tex" >/dev/null)
  gs -q -dNOPAUSE -dBATCH -sDEVICE=png16m -r300 -dTextAlphaBits=4 -dGraphicsAlphaBits=4 -sOutputFile="$OUT/$n.png" "$TMP/$n.pdf"
  echo "$OUT/$n.png"
done
rm -rf "$TMP"
