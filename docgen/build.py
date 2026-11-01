#!/usr/bin/env python3
"""Render the literate Lean file Statements.lean as a typeset LaTeX document.

usage: build.py Statements.lean paper.tex lean-toolchain lakefile.toml OUTDIR

Every line of the source appears in the output, in file order:
  * /-! ... -/ documentation comments are rendered as text (a small, strict
    Markdown subset: headings, paragraphs, '-' lists, fenced and indented code,
    `code`, **bold**, *emphasis*);
  * Lean code (theorem declarations outside comments, ```lean fences inside
    them) is reproduced verbatim, syntax-coloured, with source line numbers;
  * ```tex fences (verbatim paper excerpts) are typeset with paper.tex's own
    macros; an excerpt that does not compile in isolation falls back to a
    verbatim listing.
"""
import re, sys, hashlib, subprocess, os, json, unicodedata, datetime
import concurrent.futures as cf
from pathlib import Path

HERE = Path(__file__).resolve().parent

# ----------------------------------------------------------------------------
# small helpers
# ----------------------------------------------------------------------------
TEXT_ESC = {'\\': r'\textbackslash{}', '{': r'\{', '}': r'\}', '$': r'\$', '&': r'\&',
            '#': r'\#', '%': r'\%', '_': r'\_', '^': r'\textasciicircum{}', '~': r'\textasciitilde{}'}

def esc(s):
    return ''.join(TEXT_ESC.get(c, c) for c in s)

def esc_code_inline(s):
    """escape for \\texttt, with invisible break opportunities"""
    out = []
    for i, c in enumerate(s):
        out.append(TEXT_ESC.get(c, c))
        pass
    return ''.join(out)

def pdfstr(s):
    s = s.replace('`', '')
    return ''.join(TEXT_ESC.get(c, c) for c in s)

def anchor_safe(s):
    return re.sub(r'[^A-Za-z0-9:.\-]', '-', s)

# ----------------------------------------------------------------------------
# source segmentation
# ----------------------------------------------------------------------------
def segment(text):
    line_starts = [0] + [m.end() for m in re.finditer('\n', text)]
    import bisect
    def lineno(off):
        return bisect.bisect_right(line_starts, off)
    segs = []
    pos = 0
    def add_code(chunk, off):
        lines = chunk.split('\n')
        first = lineno(off)
        numbered = [(first + i, l) for i, l in enumerate(lines)]
        while numbered and not numbered[0][1].strip():
            numbered.pop(0)
        while numbered and not numbered[-1][1].strip():
            numbered.pop()
        if numbered:
            segs.append(('code', numbered))
    for m in re.finditer(r'/-!(.*?)-/', text, re.S):
        add_code(text[pos:m.start()], pos)
        body = m.group(1)
        first = lineno(m.start(1))
        lines = [(first + i, l) for i, l in enumerate(body.split('\n'))]
        # drop the (empty) remainder of the '/-!' line and of the '-/' line
        if lines and not lines[0][1].strip():
            lines.pop(0)
        if lines and not lines[-1][1].strip():
            lines.pop()
        segs.append(('doc', lines, lineno(m.start()), lineno(m.end() - 1)))
        pos = m.end()
    add_code(text[pos:], pos)
    return segs

# ----------------------------------------------------------------------------
# markdown block parser (strict subset)
# ----------------------------------------------------------------------------
def parse_blocks(lines):
    blocks = []
    i = 0
    n = len(lines)
    while i < n:
        ln, l = lines[i]
        if not l.strip():
            i += 1
            continue
        if l.startswith('```'):
            lang = l[3:].strip()
            body = []
            i += 1
            while i < n and lines[i][1].strip() != '```':
                body.append(lines[i])
                i += 1
            if i >= n:
                raise SystemExit(f'unterminated fence at line {ln}')
            blocks.append(('fence', lang, body, ln, lines[i][0]))
            i += 1
            continue
        m = re.match(r'^(#{1,3}) (.*)$', l)
        if m:
            blocks.append(('heading', len(m.group(1)), m.group(2).strip(), ln))
            i += 1
            continue
        if l.startswith('- '):
            items = []
            while i < n and lines[i][1].startswith('- '):
                item_ln = lines[i][0]
                text = [lines[i][1][2:].strip()]
                i += 1
                while i < n and lines[i][1].startswith('  ') and lines[i][1].strip() and not lines[i][1].startswith('    -'):
                    text.append(lines[i][1].strip())
                    i += 1
                items.append((item_ln, ' '.join(text)))
                # allow blank line between items
                j = i
                while j < n and not lines[j][1].strip():
                    j += 1
                if j < n and lines[j][1].startswith('- ') and j > i:
                    i = j
            blocks.append(('list', items, items[0][0]))
            continue
        if l.startswith('    '):
            body = []
            while i < n and (lines[i][1].startswith('    ') or (not lines[i][1].strip() and i + 1 < n and lines[i + 1][1].startswith('    '))):
                body.append(lines[i])
                i += 1
            blocks.append(('indented', body, body[0][0]))
            continue
        # paragraph
        para = []
        while i < n:
            ln2, l2 = lines[i]
            if not l2.strip() or l2.startswith('```') or l2.startswith('- ') or re.match(r'^#{1,3} ', l2):
                break
            para.append((ln2, l2))
            i += 1
        blocks.append(('para', ' '.join(x[1].strip() for x in para), para[0][0], para[-1][0]))
    return blocks

# ----------------------------------------------------------------------------
# Lean tokenizer / highlighter
# ----------------------------------------------------------------------------
KEYWORDS = {'theorem', 'lemma', 'def', 'noncomputable', 'abbrev', 'structure', 'where', 'fun',
            'let', 'in', 'if', 'then', 'else', 'by', 'match', 'with', 'do', 'have', 'show',
            'from', 'namespace', 'open', 'scoped', 'end', 'section', 'variable', 'instance',
            'class', 'deriving', 'import', 'private', 'protected', 'classical', 'Type', 'Prop',
            'Sort', 'extends', 'calc', 'exact', 'refine', 'intro', 'simp', 'rw', 'apply', 'decide',
            'omega', 'change', 'constructor', 'simpa', 'obtain', 'rcases', 'use', 'refine', 'linarith', 'norm_num', 'positivity', 'termination_by', 'decreasing_by', 'mutual', 'universe', 'at', 'only'}
LOGIC = set('∀∃→↔∧∨¬↦λ⦃⦄∑∏⋃⨆∫←⇒⟹')
TYPE_SYMS = set('ℕℤℝℂℚ')

def is_id_start(c):
    if c == '_' or c.isalpha():
        return c not in 'λΠΣ'
    o = ord(c)
    return (0x2100 <= o <= 0x214F) or (0x1D400 <= o <= 0x1D7FF)

SUBSCRIPTS = set('₀₁₂₃₄₅₆₇₈₉ₐₑₒₓₔₕₖₗₘₙₚₛₜᵢᵣᵤᵥᵦᵧᵨᵩᵪⱼ')

def is_id_char(c):
    return is_id_start(c) or c.isdigit() or c in "'!?" or c in SUBSCRIPTS

def lean_tokens(s):
    """yield (kind, text); kinds: ws, id, num, kw, logic, op, cmt, str"""
    i, n = 0, len(s)
    while i < n:
        c = s[i]
        if c in ' \t':
            j = i
            while j < n and s[j] in ' \t':
                j += 1
            yield ('ws', s[i:j]); i = j; continue
        if s.startswith('--', i):
            yield ('cmt', s[i:]); return
        if c == '"':
            j = i + 1
            while j < n and s[j] != '"':
                j += 2 if s[j] == '\\' else 1
            yield ('str', s[i:j + 1]); i = j + 1; continue
        if c == '#' and i + 1 < n and s[i + 1].isalpha():
            j = i + 1
            while j < n and s[j].isalpha():
                j += 1
            yield ('kw', s[i:j]); i = j; continue
        if c == '«':
            j = s.index('»', i)
            yield ('id', s[i:j + 1]); i = j + 1; continue
        if is_id_start(c):
            j = i
            while True:
                while j < n and is_id_char(s[j]):
                    j += 1
                if j + 1 < n and s[j] == '.' and is_id_start(s[j + 1]):
                    j += 1
                    continue
                break
            yield ('id', s[i:j]); i = j; continue
        if c.isdigit():
            j = i
            while j < n and s[j].isdigit():
                j += 1
            yield ('num', s[i:j]); i = j; continue
        if c in LOGIC:
            if c == '∃' and i + 1 < n and s[i + 1] == '!':
                yield ('logic', '∃!'); i += 2; continue
            yield ('logic', c); i += 1; continue
        yield ('op', c); i += 1

def vesc(s):
    """escape for Verbatim with commandchars=\\\\\\{\\}"""
    return s.replace('\\', '\x00BS').replace('{', '\x00LB').replace('}', '\x00RB') \
            .replace('\x00BS', r'\LBS{}').replace('\x00LB', r'\LLB{}').replace('\x00RB', r'\LRB{}')

class Highlighter:
    def __init__(self, defs):
        self.defs = defs  # resolver
        self.links_made = 0
    def line(self, s, proof_from=None):
        out = []
        col = 0
        prev = None
        for kind, t in lean_tokens(s):
            st = col
            col += len(t)
            e = vesc(t)
            if kind == 'ws':
                out.append(t); continue
            declared = prev in ('def', 'abbrev', 'structure', 'theorem', 'lemma', 'instance', 'class')
            prev = t
            if proof_from is not None and st >= proof_from:
                out.append(r'\LP{' + e + '}'); continue
            if kind == 'id':
                if t in KEYWORDS:
                    out.append(r'\LK{' + e + '}'); continue
                target = None if declared else self.defs.resolve_code(t)
                if target:
                    self.links_made += 1
                    out.append(r'\LD{' + target + '}{' + e + '}'); continue
                last = t.split('.')[-1]
                if t in TYPE_SYMS or (len(last) > 1 and last[0].isupper() and len(t) > 1 and any(ch.islower() for ch in last)):
                    out.append(r'\LT{' + e + '}'); continue
                out.append(e); continue
            if kind == 'kw':
                out.append(r'\LK{' + e + '}'); continue
            if kind == 'logic':
                out.append(r'\LL{' + e + '}'); continue
            if kind == 'cmt':
                out.append(r'\LC{' + e + '}'); continue
            out.append(e)
        return ''.join(out)

# ----------------------------------------------------------------------------
# registry of anchors (definitions, glossary, statements, contexts)
# ----------------------------------------------------------------------------
SHORT_NS = {'UniformBoundUnit', 'AllDegreesProof', 'Paper'}

class Registry:
    def __init__(self, segs):
        self.defs = {}        # D-id -> full name
        self.def_line = {}
        self.gloss = set()
        self.stmts = {}       # "Theorem 5" -> anchor
        self.stmt_keys = {}   # "thm:onb" -> ("Theorem", "5")
        self.ctx = {}         # key -> anchor
        for seg in segs:
            if seg[0] != 'doc':
                continue
            for ln, l in seg[1]:
                m = re.match(r'^### (D\d{3}w?) — `([^`]+)`\s*$', l)
                if m:
                    self.defs[m.group(1)] = m.group(2); self.def_line[m.group(1)] = ln
                m = re.match(r'^(?:### |- )(G\d\d) — ', l)
                if m:
                    self.gloss.add(m.group(1))
                m = re.match(r'^## (Theorem|Lemma|Proposition|Definition) (\d+)(?: \(`([^`]+)`\))?\s*$', l)
                if m:
                    name = f'{m.group(1)} {m.group(2)}'
                    self.stmts[name] = 'stmt:' + name.replace(' ', '-')
                    if m.group(3):
                        self.stmt_keys[m.group(3)] = (m.group(1), m.group(2))
                m = re.match(r'^### Paper context: .*\(`([^`]+)`\)\s*$', l)
                if m:
                    self.ctx[m.group(1)] = 'ctx:' + m.group(1)
        # code-name resolution
        full = {}
        short = {}
        for did, name in self.defs.items():
            full.setdefault(name, []).append(did)
            parts = name.split('.')
            if len(parts) > 1 and parts[0] in SHORT_NS:
                short.setdefault('.'.join(parts[1:]), []).append(did)
        self.full = full
        self.short = short
        self.ambiguous = {n for n in set(full) | set(short)
                          if len(set(full.get(n, [])) | set(short.get(n, []))) > 1}
    def resolve_code(self, ident):
        t = ident
        if t.startswith('@'):
            t = t[1:]
        if t.startswith('_root_.'):
            t = t[len('_root_.'):]
            cands = self.full.get(t, [])
            return 'def:' + cands[0] if len(cands) == 1 else None
        if t in self.ambiguous:
            return None
        cands = self.full.get(t) or self.short.get(t) or []
        return 'def:' + cands[0] if len(cands) == 1 else None

# ----------------------------------------------------------------------------
# inline markdown
# ----------------------------------------------------------------------------
class Inline:
    def __init__(self, reg):
        self.reg = reg
    def autolink(self, s_escaped):
        reg = self.reg
        def dl(m):
            d = m.group(1)
            return r'\hyperlink{def:%s}{%s}' % (d, d) if d in reg.defs else d
        s = re.sub(r'(?<![A-Za-z0-9])(D\d{3}w?)(?![A-Za-z0-9])', dl, s_escaped)
        def gl(m):
            g = m.group(1)
            return r'\hyperlink{gl:%s}{%s}' % (g, g) if g in reg.gloss else g
        s = re.sub(r'(?<![A-Za-z0-9])(G\d\d)(?![A-Za-z0-9])', gl, s)
        def sl(m):
            name = f'{m.group(1)} {m.group(2)}'
            if name in reg.stmts:
                return r'\hyperlink{%s}{%s}' % (reg.stmts[name], m.group(0))
            return m.group(0)
        s = re.sub(r'(?<![A-Za-z])(Theorem|Lemma|Proposition|Definition) (\d+)(?![\d.]\d)', sl, s)
        def cl(m):
            key = m.group(2).replace('\\_', '_')
            if key in reg.ctx:
                return m.group(1) + r'\hyperlink{%s}{%s}' % (reg.ctx[key], m.group(2))
            return m.group(0)
        s = re.sub(r'(Paper context / )([A-Za-z0-9]+(?:\\_[A-Za-z0-9]+)*)', cl, s)
        return s
    def text(self, s):
        out = []
        pos = 0
        for m in re.finditer(r'\*\*(.+?)\*\*|(?<![\w*])\*([A-Za-z][A-Za-z ]*[A-Za-z]|[A-Za-z])\*(?![\w*])', s):
            out.append(self.plain(s[pos:m.start()]))
            if m.group(1) is not None:
                out.append(r'\textbf{' + self.text(m.group(1)) + '}')
            else:
                out.append(r'\emph{' + self.plain(m.group(2)) + '}')
            pos = m.end()
        out.append(self.plain(s[pos:]))
        return ''.join(out)
    def plain(self, s):
        # path-like tokens (a/b) are never hyphenated; they may break after '/'
        out = []
        pos = 0
        for m in re.finditer(r'\S*[A-Za-z]/[A-Za-z]\S*', s):
            out.append(self._plain(s[pos:m.start()]))
            out.append(r'\nohy{' + esc(m.group(0)).replace('/', r'/\BO{}') + '}')
            pos = m.end()
        out.append(self._plain(s[pos:]))
        return ''.join(out)
    def _plain(self, s):
        s = re.sub(r"(?<=[^\W\d_])'(?=[A-Za-z])", '’', s)
        s = re.sub(r"(?<=[a-z]s)'(?=[\s,.;:)])", '’', s)
        s = re.sub(r"(?<=[0-9])'(?=s\b)", '’', s)
        return self.autolink(esc(s)).replace("''", "'\\kern0.12em'")
    def code(self, c, after=''):
        e = esc_code_inline(c)
        if len(c) <= 24:
            e = e.replace(' ', '~')
        reg = self.reg
        if c in reg.ctx and after.startswith(' context'):
            return r'\lclink{%s}{%s}' % (reg.ctx[c], e)
        m = re.match(r' \((D\d{3}w?)\)', after)
        if m and m.group(1) in reg.defs and reg.defs[m.group(1)].split('.')[-1] == c.split('.')[-1]:
            return r'\lclink{def:%s}{%s}' % (m.group(1), e)
        tgt = reg.resolve_code(c) if re.fullmatch(r'[\w.\'!?_«»]+', c) else None
        if tgt:
            return r'\lclink{%s}{%s}' % (tgt, e)
        return r'\lc{' + e + '}'
    def render(self, s):
        parts = re.split(r'(`[^`]+`)', s)
        out = []
        for i, p in enumerate(parts):
            if len(p) >= 2 and p.startswith('`') and p.endswith('`'):
                out.append(self.code(p[1:-1], parts[i + 1] if i + 1 < len(parts) else ''))
            else:
                out.append(self.text(p))
        return ''.join(out)

# ----------------------------------------------------------------------------
# TeX excerpt preparation
# ----------------------------------------------------------------------------
DISPLAY_ENVS = ['equation', 'align', 'gather', 'multline', 'flalign', 'alignat', 'eqnarray']

def balance_braces(t):
    depth = 0
    unmatched_close = 0
    i = 0
    while i < len(t):
        c = t[i]
        if c == '\\':
            i += 2; continue
        if c == '%':
            j = t.find('\n', i)
            i = len(t) if j < 0 else j
            continue
        if c == '{':
            depth += 1
        elif c == '}':
            if depth == 0:
                unmatched_close += 1
            else:
                depth -= 1
        i += 1
    return '{' * unmatched_close + t + '}' * depth, unmatched_close, depth

def prep_tex(tex, reg):
    notes = []
    t, uc, uo = balance_braces(tex)
    if uc or uo:
        notes.append(f'braces balanced (+{uc} open, +{uo} close)')
    for env in DISPLAY_ENVS:
        t = t.replace(r'\begin{%s}' % env, r'\begin{%s*}' % env).replace(r'\end{%s}' % env, r'\end{%s*}' % env)
    # find display regions after starring
    regions = []
    for m in re.finditer(r'\\begin\{(%s)\*\}' % '|'.join(DISPLAY_ENVS), t):
        end = t.find(r'\end{%s*}' % m.group(1), m.end())
        regions.append((m.start(), end if end >= 0 else len(t)))
    for m in re.finditer(r'\\\[', t):
        end = t.find(r'\]', m.end())
        regions.append((m.start(), end if end >= 0 else len(t)))
    def in_display(p):
        return any(a <= p <= b for a, b in regions)
    out = []
    pos = 0
    for m in re.finditer(r'\\label\{([^}]*)\}', t):
        out.append(t[pos:m.start()])
        if in_display(m.start()):
            out.append(r'\tag*{\eqkey{%s}}' % m.group(1))
        pos = m.end()
    out.append(t[pos:])
    t = ''.join(out)
    t = re.sub(r'\\(nonumber|notag)\b', '', t)
    def ref(m):
        key = m.group(1)
        if key in reg.stmt_keys:
            return reg.stmt_keys[key][1]
        return r'\refkey{%s}' % key
    t = re.sub(r'\\eqref\{([^}]*)\}', lambda m: r'\eqkey{%s}' % m.group(1), t)
    t = re.sub(r'\\ref\{([^}]*)\}', ref, t)
    def cite(m):
        opt, keys = m.group(1), m.group(2)
        s = ', '.join(k.strip() for k in keys.split(','))
        if opt:
            s += ', ' + opt
        return r'\textup{[%s]}' % s
    t = re.sub(r'\\cite(?:\[([^\]]*)\])?\{([^}]*)\}', cite, t)
    if re.match(r'\s*\{*\s*(\\\[|\\begin\{(%s)\*?\})' % '|'.join(DISPLAY_ENVS), t):
        t = '\\vspace*{-\\baselineskip}\n' + t
        notes.append('opens with a display')
    return t, notes

def paper_macros(paper_tex):
    pre = paper_tex.split(r'\begin{document}')[0]
    start = pre.index('%-------------FANCY-SYMBOLS')
    body = pre[start:]
    keep = []
    for l in body.split('\n'):
        s = l.strip()
        if not s or s.startswith('%'):
            continue
        if s.startswith((r'\newtheorem', r'\theoremstyle', r'\emergencystretch', r'\usepackage')):
            continue
        m = re.match(r'\\newcommand\{(\\[A-Za-z]+)\}', s)
        if m:
            s = r'\providecommand{%s}{}\renewcommand{%s}' % (m.group(1), m.group(1)) + s[m.end():]
        keep.append(s)
    return '\\newcommand\\PaperMacros{%\n' + '\n'.join(k.replace('#', '##') for k in keep) + '\n}\n'


# ----------------------------------------------------------------------------
# XeTeX per-character font fallback tables
# ----------------------------------------------------------------------------
def _fontdir(var, default):
    d = os.environ.get(var) or default
    return d if d.endswith('/') else d + '/'

# font directories; defaults are the Debian/Ubuntu locations
FF = _fontdir('FREEFONT_DIR', '/usr/share/fonts/truetype/freefont/')   # FreeSerif.ttf, FreeMono.ttf, ...
DV = _fontdir('DEJAVU_DIR', '/usr/share/fonts/truetype/dejavu/')       # DejaVuSans.ttf, DejaVuSansMono.ttf, ...
IN = _fontdir('INTER_DIR', '/usr/share/fonts/opentype/inter/')         # Inter-Regular.otf, ... (static OTFs)

def check_fonts():
    need = [FF + f for f in ('FreeSerif.ttf', 'FreeSerifItalic.ttf', 'FreeSerifBold.ttf', 'FreeSerifBoldItalic.ttf',
                             'FreeMono.ttf', 'FreeMonoOblique.ttf', 'FreeMonoBold.ttf', 'FreeMonoBoldOblique.ttf')]
    need += [DV + f for f in ('DejaVuSans.ttf', 'DejaVuSans-Oblique.ttf', 'DejaVuSans-Bold.ttf', 'DejaVuSans-BoldOblique.ttf',
                              'DejaVuSansMono.ttf', 'DejaVuSansMono-Oblique.ttf', 'DejaVuSansMono-Bold.ttf',
                              'DejaVuSansMono-BoldOblique.ttf')]
    need += [IN + f for f in ('Inter-Regular.otf', 'Inter-Italic.otf', 'Inter-SemiBold.otf', 'Inter-SemiBoldItalic.otf')]
    missing = [f for f in need if not os.path.isfile(f)]
    if missing:
        raise SystemExit('missing font files (set FREEFONT_DIR / DEJAVU_DIR / INTER_DIR):\n  ' + '\n  '.join(missing))
FACES = {
    'rm': {('m', 'n'): FF + 'FreeSerif.ttf', ('m', 'i'): FF + 'FreeSerifItalic.ttf',
           ('b', 'n'): FF + 'FreeSerifBold.ttf', ('b', 'i'): FF + 'FreeSerifBoldItalic.ttf'},
    'sf': {('m', 'n'): IN + 'Inter-Regular.otf', ('m', 'i'): IN + 'Inter-Italic.otf',
           ('b', 'n'): IN + 'Inter-SemiBold.otf', ('b', 'i'): IN + 'Inter-SemiBoldItalic.otf'},
    'tt': {('m', 'n'): DV + 'DejaVuSansMono.ttf', ('m', 'i'): DV + 'DejaVuSansMono-Oblique.ttf',
           ('b', 'n'): DV + 'DejaVuSansMono-Bold.ttf', ('b', 'i'): DV + 'DejaVuSansMono-BoldOblique.ttf'},
}
FB_FACES = {
    'fs': {('m', 'n'): FF + 'FreeSerif.ttf', ('m', 'i'): FF + 'FreeSerifItalic.ttf',
           ('b', 'n'): FF + 'FreeSerifBold.ttf', ('b', 'i'): FF + 'FreeSerifBoldItalic.ttf'},
    'fm': {('m', 'n'): FF + 'FreeMono.ttf', ('m', 'i'): FF + 'FreeMonoOblique.ttf',
           ('b', 'n'): FF + 'FreeMonoBold.ttf', ('b', 'i'): FF + 'FreeMonoBoldOblique.ttf'},
    'dvs': {('m', 'n'): DV + 'DejaVuSans.ttf', ('m', 'i'): DV + 'DejaVuSans-Oblique.ttf',
            ('b', 'n'): DV + 'DejaVuSans-Bold.ttf', ('b', 'i'): DV + 'DejaVuSans-BoldOblique.ttf'},
}
CHAINS = {'rm': ['fs', 'dvs', 'fm'], 'sf': ['dvs', 'fs', 'fm'], 'tt': ['dvs', 'fm', 'fs']}
# glyphs that exist in the primary font but are easily misread there
FORCE = {'\u2097': {'rm': 'dvs', 'sf': 'dvs', 'tt': 'dvs'},   # subscript l: DejaVu Sans Mono's looks like iota, FreeSerif's like 1
         '⌊': {'rm': 'dvs'}, '⌋': {'rm': 'dvs'}, '⌈': {'rm': 'dvs'}, '⌉': {'rm': 'dvs'}}   # FreeSerif's floor/ceiling are tiny
_cmaps = {}

def cmap_of(path):
    if path not in _cmaps:
        from fontTools.ttLib import TTFont
        f = TTFont(path, lazy=True)
        cm = set()
        for t in f['cmap'].tables:
            cm |= set(t.cmap.keys())
        _cmaps[path] = cm
    return _cmaps[path]

def gen_fallback(chars):
    """returns (tex, report) mapping every char missing from a primary face to a fallback face"""
    defs = {}
    missing_everywhere = []
    for ch in sorted(chars):
        cp = ord(ch)
        for fam, faces in FACES.items():
            for (w, sh), path in faces.items():
                if ch in FORCE and fam in FORCE[ch]:
                    fb = FORCE[ch][fam]
                    defs.setdefault(ch, {})[fam + w + sh] = '\\FB' + fb
                    continue
                if cp in cmap_of(path):
                    continue
                choice = None
                for fb in CHAINS[fam]:
                    for (w2, sh2) in [(w, sh), ('m', sh), (w, 'n'), ('m', 'n')]:
                        if cp in cmap_of(FB_FACES[fb][(w2, sh2)]):
                            sw = '\\FB' + fb
                            sw += '\\mdseries' if w2 == 'm' and w == 'b' else ''
                            sw += '\\upshape' if sh2 == 'n' and sh == 'i' else ''
                            choice = sw
                            break
                    if choice:
                        break
                if choice is None:
                    missing_everywhere.append((ch, fam, w, sh))
                    continue
                defs.setdefault(ch, {})[fam + w + sh] = choice
    lines = ['\\makeatletter',
             '\\def\\FB@b{b}\\def\\FB@bx{bx}\\def\\FB@sb{sb}\\def\\FB@eb{eb}\\def\\FB@ub{ub}\\def\\FB@it{it}\\def\\FB@sl{sl}',
             '\\AtBeginDocument{\\edef\\FB@ttf{\\ttdefault}\\edef\\FB@sff{\\sfdefault}}',
             '\\def\\FB@ctx{\\edef\\FB@f{\\f@family}\\edef\\FB@w{\\f@series}\\edef\\FB@s{\\f@shape}%',
             '  \\edef\\FB@key{\\ifx\\FB@f\\FB@ttf tt\\else\\ifx\\FB@f\\FB@sff sf\\else rm\\fi\\fi',
             '    \\ifx\\FB@w\\FB@b b\\else\\ifx\\FB@w\\FB@bx b\\else\\ifx\\FB@w\\FB@sb b\\else\\ifx\\FB@w\\FB@eb b\\else\\ifx\\FB@w\\FB@ub b\\else m\\fi\\fi\\fi\\fi\\fi',
             '    \\ifx\\FB@s\\FB@it i\\else\\ifx\\FB@s\\FB@sl i\\else n\\fi\\fi}}',
             '\\DeclareRobustCommand\\FB[1]{\\ifmmode\\Uchar"#1\\relax\\else\\FB@ctx',
             '  \\ifcsname FB@\\FB@key @#1\\endcsname{\\csname FB@\\FB@key @#1\\endcsname\\Uchar"#1\\relax}\\else\\Uchar"#1\\relax\\fi\\fi}',
             '\\makeatother',
             '\\AtBeginDocument{\\pdfstringdefDisableCommands{\\def\\FB#1{\\Uchar"#1}}}']
    for ch, ctxs in sorted(defs.items()):
        hx = '%04X' % ord(ch)
        for key, sw in sorted(ctxs.items()):
            lines.append('\\expandafter\\def\\csname FB@%s@%s\\endcsname{%s}' % (key, hx, sw))
        lines.append('\\newunicodechar{%s}{\\FB{%s}}' % (ch, hx))
    return '\n'.join(lines) + '\n', missing_everywhere, defs

# ----------------------------------------------------------------------------
# document assembly
# ----------------------------------------------------------------------------
def needspace(nlines, extra):
    k = min(nlines + extra + 1, 44)
    return r'\Needspace{%d\baselineskip}' % k


class Doc:
    def __init__(self, src_text, reg, inline, hl, tex_ok):
        self.reg = reg
        self.inl = inline
        self.hl = hl
        self.tex_ok = tex_ok        # excerpt index -> bool
        self.out = []
        self.cur_stmt = None        # ("Theorem", "5")
        self.coverage = {}
        self.tex_index = 0
        self.title = None
        self.intro = []
        self.in_intro = True
        self.stats = dict(lean_lines=0, theorem_segments=0, fences_lean=0, fences_tex=0,
                          tex_typeset=0, tex_verbatim=0, check_lines=0)

    def emit(self, s):
        if self.in_intro:
            self.intro.append(s)
        else:
            self.out.append(s)

    # ---- code (outside comments)
    def code_segment(self, numbered):
        first = numbered[0][0]
        last = numbered[-1][0]
        text = [l for _, l in numbered]
        head = text[0]
        self.stats['lean_lines'] += len(text)
        if head.startswith('theorem '):
            self.stats['theorem_segments'] += 1
            name = head.split()[1]
            # proof term: everything after the last ':=' that ends a line
            proof_line = None
            for k in range(len(text) - 1, -1, -1):
                if re.search(r':=\s*$', text[k]):
                    proof_line = k
                    break
            body = []
            for k, l in enumerate(text):
                if proof_line is not None and k == proof_line:
                    col = l.rstrip().rfind(':=')
                    body.append(self.hl.line(l, proof_from=col))
                elif proof_line is not None and k > proof_line:
                    body.append(self.hl.line(l, proof_from=0))
                else:
                    body.append(self.hl.line(l))
            title = 'Lean statement'
            meta = r'\texttt{\color{leanrule}%s}\hspace{0.6em}lines %d–%d' % (esc(name), first, last)
            self.emit(needspace(len(text), 3))
            self.emit(r'\begin{leanstmt}{%s}{%s}' % (title, meta))
            self.emit(r'\begin{LeanVerb}[firstnumber=%d]' % first)
            self.emit('\n'.join(body))
            self.emit(r'\end{LeanVerb}')
            self.emit(r'\end{leanstmt}')
            if self.in_intro:
                pass
            return
        label = 'Lean'
        if head.startswith('#check'):
            label = r'Lean · \#check'
            self.stats['check_lines'] += sum(1 for l in text if l.startswith('#check'))
        elif head.startswith('import'):
            label = 'Lean · file header'
        elif head.startswith('end '):
            label = 'Lean · end of file'
        elif head.startswith('namespace'):
            label = 'Lean · namespace'
        self.emit(needspace(len(text), 3))
        self.emit(r'\begin{leanmisc}{%s}{lines %d–%d}' % (label, first, last) if first != last else
                  r'\begin{leanmisc}{%s}{line %d}' % (label, first))
        self.emit(r'\begin{LeanVerb}[firstnumber=%d]' % first)
        self.emit('\n'.join(self.hl.line(l) for l in text))
        self.emit(r'\end{LeanVerb}')
        self.emit(r'\end{leanmisc}')

    # ---- documentation comments
    def doc_segment(self, lines, start_line, end_line):
        blocks = parse_blocks(lines)
        k = 0
        while k < len(blocks):
            b = blocks[k]
            nxt = blocks[k + 1] if k + 1 < len(blocks) else None
            if b[0] == 'para' and nxt and nxt[0] == 'fence' and nxt[1] == 'tex':
                self.tex_box(b, nxt)
                k += 2
                continue
            if b[0] == 'heading' and b[1] == 3 and re.match(r'^D\d{3}w? — ', b[2]):
                extra = 0
                for b2 in blocks[k + 1:]:
                    if b2[0] == 'heading':
                        break
                    if b2[0] == 'fence':
                        self.emit(needspace(len(b2[2]), 5 + extra))
                        break
                    if b2[0] == 'para':
                        extra += (b2[3] - b2[2] + 1) + 1
            self.block(b)
            k += 1

    def block(self, b):
        kind = b[0]
        if kind == 'heading':
            self.heading(b[1], b[2], b[3])
        elif kind == 'para':
            self.emit(self.inl.render(b[1]) + '\n')
        elif kind == 'list':
            self.emit(r'\begin{itemize}')
            for ln, text in b[1]:
                anchor = ''
                m = re.match(r'^(G\d\d) — ', text)
                if m:
                    anchor = r'\phantomsection\hypertarget{gl:%s}{}' % m.group(1)
                self.emit(r'\item ' + anchor + self.inl.render(text))
            self.emit(r'\end{itemize}')
        elif kind == 'indented':
            body = [l[4:] if l.startswith('    ') else l for _, l in b[1]]
            self.emit(r'\begin{ProseVerb}')
            self.emit('\n'.join(body))
            self.emit(r'\end{ProseVerb}')
        elif kind == 'fence':
            lang, body, ln = b[1], b[2], b[3]
            if lang == 'lean':
                self.stats['fences_lean'] += 1
                self.stats['lean_lines'] += len(body)
                self.emit(needspace(len(body), 2))
                self.emit(r'\begin{leandef}{}')
                self.emit(r'\begin{LeanVerb}[firstnumber=%d]' % body[0][0])
                self.emit('\n'.join(self.hl.line(l) for _, l in body))
                self.emit(r'\end{LeanVerb}')
                self.emit(r'\end{leandef}')
            elif lang == 'tex':
                self.tex_box(None, b)
            else:
                self.emit(r'\begin{leandef}{}')
                self.emit(r'\begin{TexVerb}[firstnumber=%d]' % body[0][0])
                self.emit('\n'.join(l for _, l in body))
                self.emit(r'\end{TexVerb}')
                self.emit(r'\end{leandef}')

    def tex_box(self, lead, fence):
        self.stats['fences_tex'] += 1
        idx = self.tex_index
        self.tex_index += 1
        body = fence[2]
        first, last = body[0][0], body[-1][0]
        raw = '\n'.join(l for _, l in body)
        title, meta = 'Paper excerpt', ''
        lead_text = lead[1] if lead else ''
        statement = False
        if lead_text == 'Paper statement (verbatim TeX):':
            title = 'Paper statement'
            statement = True
        else:
            m = re.match(r'^Original paper definition/context \(`([^`]+)`, verbatim TeX\):$', lead_text)
            if m:
                title = 'Original paper definition/context'
                meta = esc(m.group(1)) + r' \textperiodcentered{} '
            elif lead_text:
                # unknown lead-in: keep it as a paragraph
                self.emit(self.inl.render(lead_text) + '\n')
        ok, prepared = self.tex_ok[idx]
        if ok:
            self.stats['tex_typeset'] += 1
            meta += r'typeset from the verbatim TeX at lines %d–%d' % (first, last)
            self.emit(needspace(min(len(body), 12), 3))
            self.emit(r'\begin{paperbox}{%s}{%s}' % (title, meta))
            if statement and self.cur_stmt:
                self.emit(r'\setcounter{theorem}{%d}' % (int(self.cur_stmt[1]) - 1))
            self.emit(prepared)
            self.emit(r'\end{paperbox}')
        else:
            self.stats['tex_verbatim'] += 1
            meta += r'verbatim TeX (does not compile in isolation), lines %d–%d' % (first, last)
            self.emit(r'\begin{texverbbox}{%s}{%s}' % (title, meta))
            self.emit(r'\begin{TexVerb}[firstnumber=%d]' % first)
            self.emit(raw)
            self.emit(r'\end{TexVerb}')
            self.emit(r'\end{texverbbox}')

    def heading(self, level, text, ln):
        reg = self.reg
        if level == 1:
            self.title = text
            return
        if level == 2:
            m = re.match(r'^(Theorem|Lemma|Proposition|Definition) (\d+)(?: \(`([^`]+)`\))?\s*$', text)
            if m:
                self.in_intro = False
                name = f'{m.group(1)} {m.group(2)}'
                key = m.group(3) or ''
                self.cur_stmt = (m.group(1), m.group(2))
                cov = self.coverage.get(name, '')
                chip = ''
                if cov:
                    color = 'amber' if cov == 'component-only' else ('green' if cov.startswith('direct') else 'blue')
                    chip = r'\covchip{%s}{coverage: %s}' % (color, esc(cov))
                pdf = name + (f' ({key})' if key else '')
                self.emit(r'\stmthead{%s}{%s}{%s}{%s}{%d}{%s}' % (
                    name, esc_code_inline(key), reg.stmts[name], chip, ln, pdfstr(pdf)))
                return
            anchor = 'part:' + anchor_safe(text)[:40]
            newpage = '1'
            if self.in_intro:
                newpage = '0'
            if text.startswith('Lean and Mathlib'):
                self.in_intro = False
            self.cur_stmt = None
            self.emit(r'\parthead{%s}{%s}{%d}{%s}{%s}' % (self.inl.render(text), anchor, ln, pdfstr(text), newpage))
            return
        # level 3
        m = re.match(r'^(D\d{3}w?) — `([^`]+)`\s*$', text)
        if m:
            did = m.group(1)
            self.emit(r'\defhead{%s}{%s}{def:%s}{%d}{%s}' % (
                did, esc_code_inline(m.group(2)), did, ln, pdfstr(f'{did} — {m.group(2)}')))
            return
        m = re.match(r'^(G\d\d) — (.*)$', text)
        if m:
            g = m.group(1)
            self.emit(r'\glosshead{%s}{%s}{gl:%s}{%d}{%s}' % (
                g, self.inl.render(m.group(2)), g, ln, pdfstr(text)))
            return
        m = re.match(r'^Paper context: (.*) \(`([^`]+)`\)\s*$', text)
        if m:
            key = m.group(2)
            self.emit(r'\ctxhead{%s}{%s}{%s}{%d}{%s}' % (
                self.inl.render(m.group(1)), esc_code_inline(key), reg.ctx[key], ln,
                pdfstr('Paper context: ' + m.group(1))))
            return
        self.emit(r'\subhead{%s}{%s}{%d}{%s}' % (self.inl.render(text), 'sub:%d' % ln, ln, pdfstr(text)))


def scan_coverage(segs):
    cov = {}
    cur = None
    for seg in segs:
        if seg[0] != 'doc':
            continue
        for ln, l in seg[1]:
            m = re.match(r'^## (Theorem|Lemma|Proposition|Definition) (\d+)', l)
            if m:
                cur = f'{m.group(1)} {m.group(2)}'
                continue
            if l.startswith('## '):
                cur = None
            m = re.match(r'^Coverage: `([^`]+)`', l)
            if m and cur and cur not in cov:
                cov[cur] = m.group(1)
    return cov


def collect_tex(segs):
    out = []
    for seg in segs:
        if seg[0] != 'doc':
            continue
        for b in parse_blocks(seg[1]):
            if b[0] == 'fence' and b[1] == 'tex':
                out.append('\n'.join(l for _, l in b[2]))
    return out


def compile_test(args):
    idx, prepared, preamble, macros, workdir = args
    d = Path(workdir) / f'tex{idx:02d}'
    d.mkdir(parents=True, exist_ok=True)
    doc = preamble + macros + '\\begin{document}\n\\begin{paperbox}{test}{}\n\\setcounter{theorem}{0}\n' + \
        prepared + '\n\\end{paperbox}\n\\end{document}\n'
    (d / 't.tex').write_text(doc, encoding='utf-8')
    r = subprocess.run(['xelatex', '-interaction=nonstopmode', '-halt-on-error', 't.tex'],
                       cwd=d, capture_output=True, text=True, errors='replace', timeout=300)
    log = (d / 't.log').read_text(encoding='utf-8', errors='replace') if (d / 't.log').exists() else ''
    errs = [l for l in log.split('\n') if l.startswith('! ')][:3]
    ok = r.returncode == 0 and not errs and (d / 't.pdf').exists()
    if not ok:
        tail = [l for l in (r.stdout + r.stderr).strip().split('\n') if l.strip()][-4:]
        errs = errs + [f'exit code {r.returncode}', 'last output: ' + ' | '.join(tail), f'log: {d / "t.log"}']
    return idx, ok, errs


def main():
    src_p, paper_p, tool_p, lake_p, outdir = map(Path, sys.argv[1:6])
    outdir.mkdir(parents=True, exist_ok=True)
    raw = src_p.read_bytes()
    text = raw.decode('utf-8')
    sha = hashlib.sha256(raw).hexdigest()
    nlines = text.count('\n') + (0 if text.endswith('\n') else 1)
    segs = segment(text)
    reg = Registry(segs)
    inline = Inline(reg)
    hl = Highlighter(reg)

    check_fonts()
    preamble = (HERE / 'preamble.tex').read_text(encoding='utf-8')
    preamble = preamble.replace('@FREEFONT_DIR@', FF).replace('@DEJAVU_DIR@', DV).replace('@INTER_DIR@', IN)
    extra = set('’…·—–“”‘')
    charset = set(ch for ch in text if ord(ch) > 127) | extra
    fbtex, nowhere, fbdefs = gen_fallback(charset)
    if nowhere:
        chars = sorted({c for c, *_ in nowhere})
        print('GLYPHS MISSING IN EVERY FONT: ' + ' '.join(f'{c} (U+{ord(c):04X})' for c in chars), file=sys.stderr)
    print(f'fallback: {len(fbdefs)} characters remapped in some context', file=sys.stderr)
    preamble = preamble.replace('\\input{fallback.tex}', fbtex)
    macros = paper_macros(paper_p.read_text(encoding='utf-8'))

    # ---- prepare + test-compile every TeX excerpt
    texs = collect_tex(segs)
    prepared = []
    prep_notes = []
    for t in texs:
        p, notes = prep_tex(t, reg)
        prepared.append(p)
        prep_notes.append(notes)
    tex_ok = {}
    work = outdir / 'textest'
    with cf.ThreadPoolExecutor(max_workers=8) as ex:
        for idx, ok, errs in ex.map(compile_test, [(i, p, preamble, macros, str(work)) for i, p in enumerate(prepared)]):
            tex_ok[idx] = (ok, prepared[idx])
            if not ok:
                print(f'[tex {idx}] FALLBACK to verbatim: {errs}', file=sys.stderr)
            if prep_notes[idx]:
                print(f'[tex {idx}] note: {prep_notes[idx]}', file=sys.stderr)

    doc = Doc(text, reg, inline, hl, tex_ok)
    doc.coverage = scan_coverage(segs)
    for i, seg in enumerate(segs):
        nxt = segs[i + 1] if i + 1 < len(segs) else None
        if (seg[0] == 'doc' and nxt and nxt[0] == 'code' and nxt[1][0][1].startswith('theorem ')
                and len(seg[1]) <= 14 and not any(l.startswith('#') for _, l in seg[1])):
            doc.emit(needspace(len(seg[1]) + len(nxt[1]), 4))
        if seg[0] == 'code':
            doc.code_segment(seg[1])
        else:
            doc.doc_segment(seg[1], seg[2], seg[3])

    toolchain = tool_p.read_text().strip()
    mrev = re.search(r'rev\s*=\s*"([^"]+)"', lake_p.read_text())
    mathlib = mrev.group(1) if mrev else '?'
    today = datetime.date.today().strftime('%-d %B %Y')
    n_def = len(reg.defs)
    title = doc.title or 'Statements.lean'

    front = []
    front.append(r'\begin{document}')
    front.append(r'\thispagestyle{plain}')
    front.append(r'\pdfbookmark[1]{Title}{title}')
    front.append(r'{\sffamily\fontsize{8.5}{10}\selectfont\color{muted}\MakeUppercase{Rudin’s problem \textperiodcentered{} Lean 4 formalization of arXiv:2610.14160}}\par\vspace{6pt}')
    front.append(r'{\sffamily\bfseries\color{accent}\fontsize{22}{27}\selectfont %s\par}\vspace{8pt}' % esc(title))
    front.append(r'{\sffamily\fontsize{9.5}{12}\selectfont\color{muted}A typeset rendering of \texttt{PaperFormalization/Statements.lean}\par}\vspace{10pt}')
    meta_rows = [
        ('Source file', r'\texttt{PaperFormalization/Statements.lean} (%s lines)' % format(nlines, ',')),
        ('SHA-256', r'{\ttfamily\small %s}' % sha),
        ('Lean toolchain', r'\texttt{%s}' % esc(toolchain)),
        ('Mathlib', r'\texttt{%s} (\texttt{lakefile.toml})' % esc(mathlib)),
        ('Rendered', today),
    ]
    front.append(r'{\sffamily\fontsize{8.5}{11}\selectfont\renewcommand{\arraystretch}{1.15}\begin{tabular}{@{}>{\color{muted}}l@{\hspace{1.2em}}l@{}}')
    front.append('\n'.join(r'%s & %s\\' % r for r in meta_rows))
    front.append(r'\end{tabular}}\par\vspace{12pt}')
    front.append(r'\vspace{4pt}')
    front.append(r'\begin{notebox}')
    front.append(r'{\bfseries\color{accent}About this rendering.}\enspace '
                 r'Every line of \texttt{Statements.lean} appears below, in file order. '
                 r'Documentation comments (\texttt{/-!}\,…\,\texttt{-/}) are set as text. '
                 r'Lean code is reproduced character for character, with the file’s line numbers in the margin; '
                 r'a \textcolor{paperrule}{\ttfamily\symbol{"21AA}} marks where a line too long for the page was wrapped. '
                 r'The paper excerpts, which the file quotes as verbatim TeX, are typeset here with the macros of the '
                 r'\texttt{paper.tex} preamble; equation labels are shown as their keys, e.g.\ \eqkey{eq:saw}, and '
                 r'references to numbered statements by their numbers. Blue text links to definitions (D\,nnn), '
                 r'glossary entries (G\,nn) and statements.'
                 r'\par\medskip'
                 r'{\fontsize{7.5}{10}\selectfont'
                 r'\colorbox{paperbg}{\textcolor{paperrule}{\rule{2pt}{6pt}}\,\strut paper excerpt}\enspace'
                 r'\colorbox{leanbg}{\textcolor{leanrule}{\rule{2pt}{6pt}}\,\strut Lean statement (\texttt{theorem})}\enspace'
                 r'\fcolorbox{defframe}{defbg}{\strut Lean definition body (D-block)}\enspace'
                 r'\colorbox{miscbg}{\textcolor{faint}{\rule{2pt}{6pt}}\,\strut other Lean code}\enspace'
                 r'\LK{keyword}\enspace\LL{∀ → ∧}\enspace\LT{ℕ Finset}\enspace\LD{def:D001}{linked definition}\enspace\LP{proof term}}')
    front.append(r'\end{notebox}')
    front.append(r'\clearpage')
    front.append(r'\pdfbookmark[1]{Contents}{contents}')
    front.append(r'{\sffamily\bfseries\color{accent}\fontsize{15}{19}\selectfont Contents\par}\vspace{2pt}{\noindent\partrule}\par\vspace{6pt}')
    front.append(r'\makeatletter\@starttoc{toc}\makeatother')
    front.append(r'\parthead{File header}{part:file-header}{1}{File header}{1}')
    front.append('\n'.join(doc.intro))

    body = '\n'.join(front) + '\n' + '\n'.join(doc.out) + '\n\\end{document}\n'
    full = preamble + macros + body
    (outdir / 'formalization.tex').write_text(full, encoding='utf-8')
    stats = dict(doc.stats, defs=n_def, links=hl.links_made, sha256=sha, lines=nlines,
                 tex_fallbacks=[i for i, (ok, _) in tex_ok.items() if not ok])
    (outdir / 'stats.json').write_text(json.dumps(stats, indent=1))
    print(json.dumps(stats, indent=1))


if __name__ == '__main__':
    main()
