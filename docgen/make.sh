#!/usr/bin/env bash
# usage: make.sh PAPERFORMALIZATION_DIR [BUILD_DIR]
#
#   make.sh PaperFormalization          writes PaperFormalization/formalization.pdf;
#                                        intermediate files go to a temporary directory
#   make.sh PaperFormalization build    writes build/formalization.pdf and keeps every
#                                        intermediate file (formalization.tex, logs, …) in build/
#
# Exit status is non-zero if the PDF could not be built, or if some character could not be
# rendered by any of the fonts (the PDF is still written, but would be missing those glyphs).
set -euo pipefail
if [ $# -lt 1 ] || [ $# -gt 2 ]; then
  echo "usage: $(basename "$0") PAPERFORMALIZATION_DIR [BUILD_DIR]" >&2
  exit 2
fi
S="$(realpath "$1")"
T="${RENDER_TOOL_DIR:-$(dirname "$(realpath "$0")")}"
if [ $# -eq 2 ]; then
  mkdir -p "$2"
  B="$(realpath "$2")"
  OUT="$B/formalization.pdf"
else
  B="$(mktemp -d "${TMPDIR:-/tmp}/render-statements.XXXXXX")"
  OUT="$S/formalization.pdf"
fi

python3 -I "$T/build.py" "$S/PaperFormalization/Statements.lean" "$S/paper.tex" "$S/lean-toolchain" "$S/lakefile.toml" "$B" > "$B/stats.txt" 2>&1 \
  || { cat "$B/stats.txt"; echo "build.py failed; files kept in $B" >&2; exit 1; }
cd "$B"
for i in 1 2 3; do
  xelatex -interaction=nonstopmode -halt-on-error formalization.tex > "run$i.log" 2>&1 \
    || { grep -n -A4 '^!' formalization.log | head -20; echo "xelatex failed; files kept in $B" >&2; exit 1; }
done

missing=$(grep -c 'Missing character' formalization.log || true)
echo "pages: $(pdfinfo formalization.pdf | awk '/Pages/{print $2}')  overfull: $(grep -c Overfull formalization.log || true)  missing-chars: $missing  undefined-refs: $(grep -c 'undefined' formalization.log || true)"
grep -h 'FALLBACK\|MISSING\|note:' stats.txt || true

if [ "$OUT" != "$B/formalization.pdf" ]; then
  cp formalization.pdf "$OUT"
  if [ "$missing" -eq 0 ]; then cd /; rm -rf "$B"; else echo "intermediate files kept in $B" >&2; fi
fi
echo "wrote $OUT"
if [ "$missing" -ne 0 ]; then
  echo "ERROR: $missing character(s) could not be rendered by any font; see 'Missing character' in the log." >&2
  exit 1
fi
