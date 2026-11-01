# Rendering Statements.lean to formalization.pdf

## With Nix (recommended)

The flake pins nixpkgs (nixos-26.05) and brings XeLaTeX (TeX Live 2025), Python with
fontTools, poppler and the fonts, so nothing else needs to be installed. Run the
commands from this folder.

    # build the PDF: writes ../formalization.pdf (intermediate files go to a temporary directory)
    nix run . -- ..

    # check it: every Lean code line present in order, prose aligned word by word; prints PASS or FAIL
    nix run .#check -- ../PaperFormalization/Statements.lean ../formalization.pdf

    # or a shell with xelatex, python3 + fontTools, pdftotext and the font variables set
    nix develop
    ./make.sh ..

To keep the intermediate files (formalization.tex, logs, per-excerpt test builds) for
debugging, give a build folder as a second argument, e.g. `nix run . -- .. /tmp/render-build`;
the PDF is then written there instead of to `..`. Don't use the repository itself as the
build folder, or those files end up in it.

Both commands report problems and exit non-zero:

- the build refuses to render if a source-line citation in Statements.lean is wrong
  (see "Source citations" below);
- the build fails if some character could not be rendered by any font (the PDF is still
  written, but would be missing those glyphs);
- a paper excerpt that does not compile on its own is shown as verbatim TeX and reported
  as `[tex N] FALLBACK to verbatim`, with its error and the path of its log;
- the check prints `FAIL` and lists any missing code line, unmatched word or wrong citation.

## Source citations

Statements.lean cites lines of Core.lean and Compatibility.lean: each D-block's
"`Core.lean:621`", and prose such as "`thm_onb` (Core.lean:17679)". These go stale whenever
the cited file changes above them, so they are verified mechanically:

    # report
    nix run .#citations -- ../PaperFormalization/Statements.lean
    # rewrite stale line numbers in place (only the numbers change; the line count does not)
    nix run .#citations -- ../PaperFormalization/Statements.lean --fix

A D-block's code must appear verbatim in the cited file starting at the cited line. A prose
citation's line must declare the identifier named just before it (or lie in that
declaration's docstring); a citation of a construction rather than a named declaration must
point at a declaration that uses the identifiers the sentence mentions. `--fix` changes a
number only when the correct line is unambiguous and lists anything else for a human.

`warning: Git tree … is dirty` only means the repository has uncommitted changes. Nix
sees only files that git tracks, so `git add` new files in this folder before running.

## What the renderer does

`make.sh` runs `build.py` (Statements.lean → formalization.tex) and then XeLaTeX three
times. `check.py` confirms from the PDF's text layer that every Lean code line of the
source appears, in order, and aligns the prose word by word.

- `/-! … -/` comments are set as prose (headings, paragraphs, `- ` lists, fenced and
  indented code, `code`, **bold**, *emphasis*; everything else is literal text).
- Lean code (theorem declarations outside comments, ```` ```lean ```` fences inside them)
  is reproduced verbatim with the file's line numbers; over-long lines are soft-wrapped
  and marked with ↪. Identifiers that name a displayed definition link to its D-block;
  names that are ambiguous (e.g. root `ThmBox` vs `UniformBoundUnit.ThmBox`) are not linked.
- ```` ```tex ```` fences are typeset with the macros of `paper.tex`'s preamble. Each
  excerpt is first compiled on its own; one that fails falls back to a verbatim listing.
  Unbalanced grouping braces are balanced invisibly; display `\label`s are shown as
  their keys; `\ref` to a numbered statement prints its number.
- XeTeX has no automatic font fallback, so `build.py` reads each font's character map
  (fontTools) and routes characters a font lacks to a fallback font (FreeSerif, DejaVu
  Sans, FreeMono), per family and style.
