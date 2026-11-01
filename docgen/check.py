#!/usr/bin/env python3
"""Fidelity check of a rendered PDF against Statements.lean.

usage: check.py Statements.lean formalization.pdf

1. Every non-blank Lean code line (outside /-! -/ comments, and inside ```lean fences)
   must appear in the PDF's text layer, in order (whitespace, margin line numbers and the
   ↪ wrap marker ignored).
2. The prose of the doc comments is aligned word by word with the PDF text. The renderer
   restyles a few things on purpose (box labels in capitals, "Paper context" headings shown
   as key + title); those are normalised here, so any word left unmatched is reported.

Exit status 0 = PASS, 1 = FAIL.
"""
import difflib, re, subprocess, sys, unicodedata

src = unicodedata.normalize('NFC', open(sys.argv[1], encoding='utf-8').read())
txt = subprocess.run(['pdftotext', '-enc', 'UTF-8', sys.argv[2], '-'],
                     capture_output=True, text=True, check=True).stdout
txt = unicodedata.normalize('NFC', txt)
txt = re.sub(r'(?m)^\d+$', '', txt)                      # margin line numbers
LIG = {'ﬁ': 'fi', 'ﬂ': 'fl', 'ﬀ': 'ff', 'ﬃ': 'ffi', 'ﬄ': 'ffl'}
for a, b in LIG.items():
    txt = txt.replace(a, b)

# ---------------------------------------------------------------- 1. code lines
flat = re.sub(r'\s+', '', txt.replace('↪', ''))
code_lines, pos = [], 0
for m in re.finditer(r'/-!(.*?)-/', src, re.S):
    code_lines += src[pos:m.start()].split('\n')
    for f in re.findall(r'```lean\n(.*?)```', m.group(1), re.S):
        code_lines += f.split('\n')
    pos = m.end()
code_lines += src[pos:].split('\n')
code_lines = [l for l in code_lines if l.strip()]
missing, cursor = [], 0
for l in code_lines:
    key = re.sub(r'\s+', '', l)
    for a, b in LIG.items():
        key = key.replace(a, b)
    k = flat.find(key, cursor)
    if k < 0:
        missing.append((l, 'absent' if flat.find(key) < 0 else 'out of order'))
    else:
        cursor = k
print(f'code lines checked: {len(code_lines)}; not found in order: {len(missing)}')
for l, why in missing[:20]:
    print('   -', why, '|', l)

# ---------------------------------------------------------------- 2. prose words
def norm_source_prose(d):
    d = re.sub(r'```.*?```', ' ', d, flags=re.S)                       # fences checked elsewhere
    # "### Paper context: Title (`key`)" is displayed as "PAPER CONTEXT key" + "Title"
    d = re.sub(r'(?m)^### Paper context: (.*) \(`([^`]+)`\)\s*$', r'Paper context \2 \1', d)
    # TeX lead-ins become box labels: "PAPER STATEMENT …" / "ORIGINAL PAPER DEFINITION/CONTEXT file:lines …"
    d = re.sub(r'(?m)^Paper statement \(verbatim TeX\):$', 'Paper statement', d)
    d = re.sub(r'(?m)^Original paper definition/context \(`([^`]+)`, verbatim TeX\):$',
               r'Original paper definition/context \1', d)
    d = re.sub(r'(?m)^#+ ', '', d)
    return d.replace('`', '')                                         # "`abbrev`s" reads "abbrevs"

WORD = r'[A-Za-z][A-Za-z0-9]{3,}'
prose = '\n'.join(norm_source_prose(d) for d in re.findall(r'/-!(.*?)-/', src, re.S))
words = [w.lower() for w in re.findall(WORD, prose.replace('_', ' '))]
pdftxt = re.sub(r'-\n', '', txt)                                       # undo hyphenation at line ends
pdfwords = [w.lower() for w in re.findall(WORD, pdftxt.replace('_', ' '))]
sm = difflib.SequenceMatcher(None, words, pdfwords, autojunk=False)
matched = sum(b.size for b in sm.get_matching_blocks())
unmatched, last = [], 0
for b in sm.get_matching_blocks():
    if b.a > last:
        unmatched.append(' '.join(words[last:b.a]))
    last = b.a + b.size
print(f'prose words checked: {len(words)}; matched in order: {matched}; unmatched runs: {len(unmatched)}')
for u in unmatched[:40]:
    print('   -', u[:150])

ok = not missing and not unmatched
print('PASS' if ok else 'FAIL')
sys.exit(0 if ok else 1)
