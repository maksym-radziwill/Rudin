#!/usr/bin/env python3
"""Verify the source-line citations in Statements.lean against the files they cite.

usage: citations.py Statements.lean [--fix]

Statements.lean cites source lines in two ways, and both are checked:

* D-blocks: "### Dnnn — `name`" followed by "`Core.lean:621` · Used by …" and a ```lean
  block. The block must appear verbatim in Core.lean starting at line 621.
* Prose: "`thm_onb` (Core.lean:17675)", "(private `name`, Core.lean:14755)",
  "`a`, `b` (Core.lean:9595, 9598)". Each cited line must be the declaration of the
  identifier the citation refers to (the nearest backticked identifiers before it), or
  part of its docstring/attribute header.

Cited files are looked up next to Statements.lean. With --fix, every wrong citation whose
correct line is unambiguous is rewritten in place (only the number changes, so the file
keeps its line count); anything else is reported for a human. Exit status 0 = all
citations correct (after fixing, if --fix), 1 otherwise.
"""
import re
import sys
from pathlib import Path

CITE = r'((?:Core|Compatibility)\.lean):(\d+)'
DECL_KW = r'(?:theorem|lemma|def|abbrev|structure|inductive|class|instance|opaque|axiom)'
DECL_PREFIX = r'^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|partial|unsafe|nonrec)\s+)*'


def load_sources(base):
    cache = {}

    def get(fname):
        if fname not in cache:
            p = base / fname
            cache[fname] = p.read_text(encoding='utf-8').split('\n') if p.exists() else None
        return cache[fname]
    return get


def decl_lines(src, ident):
    """1-based lines that declare `ident` (matched on its last name component)."""
    last = re.escape(ident.split('.')[-1])
    pat = re.compile(DECL_PREFIX + DECL_KW + r'\s+(?:[\w.]+\.)?' + last + r'(?![\w.\'!?])')
    return [i + 1 for i, l in enumerate(src) if pat.match(l)]


ANY_DECL = re.compile(DECL_PREFIX + DECL_KW + r'\s+[\w.\'!?«»]+')


def construction_lines(src, idents):
    """1-based lines of declarations whose text (up to the next declaration) uses every identifier."""
    starts = [i for i, l in enumerate(src) if ANY_DECL.match(l)] + [len(src)]
    hits = []
    for a, b in zip(starts, starts[1:]):
        body = '\n'.join(src[a:b])
        if all(re.search(r'(?<![\w.])' + re.escape(t) + r'(?![\w\'!?])', body) or ('.' + t) in body for t in idents):
            hits.append(a + 1)
    return hits


def header_reaches(src, line, decl):
    """True if `line` lies in the docstring/attribute header directly above declaration `decl`."""
    if line == decl:
        return True
    if not (0 < line < decl):
        return False
    in_doc = False
    for k in range(line - 1, decl - 1):
        s = src[k].strip()
        if in_doc:
            if '-/' in s:
                in_doc = False
            continue
        if s.startswith('/--') or s.startswith('/-!') or s.startswith('/-'):
            in_doc = '-/' not in s[2:]
            continue
        if s == '' or s.startswith('@[') or s.startswith('--'):
            continue
        return False
    return True


def check(stmt_text, get):
    """Return a list of findings: dict(kind, what, file, cited, status, correct, span)."""
    out = []
    # ---- D-blocks
    dspans = []
    for m in re.finditer(r'^### (D\d{3}w?) — `([^`]+)`\n(.*?)(?=^### |^## |^-/)', stmt_text, re.M | re.S):
        did, name, body = m.groups()
        body_start = m.start(3)
        c = re.search('`' + CITE + '`', body)
        fence = re.search(r'```lean\n(.*?)```', body, re.S)
        if not c or not fence:
            out.append(dict(kind='D-block', what=f'{did} {name}', file='?', cited=None,
                            status='no citation or code', correct=None, span=None))
            continue
        dspans.append((m.start(), m.end()))
        fname, cited = c.group(1), int(c.group(2))
        span = (body_start + c.start(2), body_start + c.end(2))
        src = get(fname)
        shown = fence.group(1).rstrip('\n').split('\n')
        if src is None:
            out.append(dict(kind='D-block', what=f'{did} {name}', file=fname, cited=cited,
                            status=f'{fname} not found next to Statements.lean', correct=None, span=span))
            continue
        if src[cited - 1:cited - 1 + len(shown)] == shown:
            status, correct = 'ok', cited
        else:
            hits = [i + 1 for i in range(len(src)) if src[i:i + len(shown)] == shown]
            if len(hits) == 1:
                status, correct = 'stale', hits[0]
            elif hits:
                status, correct = f'code appears at several lines {hits}', None
            else:
                status, correct = 'CODE NOT FOUND in the cited file (the D-block differs from the source)', None
        out.append(dict(kind='D-block', what=f'{did} {name}', file=fname, cited=cited,
                        status=status, correct=correct, span=span))

    def in_dblock_header(pos):
        return any(a <= pos < b for a, b in dspans)

    # ---- prose citations: "(…Core.lean:N[, M…])" not belonging to a D-block header line
    for m in re.finditer(CITE + r'((?:,\s*\d+)*)', stmt_text):
        line_start = stmt_text.rfind('\n', 0, m.start()) + 1
        line = stmt_text[line_start:stmt_text.find('\n', m.start())]
        if in_dblock_header(m.start()) and re.match(r'^`' + CITE + r'` · ', line):
            continue
        fname = m.group(1)
        nums = [(int(m.group(2)), (m.start(2), m.end(2)))]
        for extra in re.finditer(r'\d+', m.group(3)):
            nums.append((int(extra.group()), (m.start(3) + extra.start(), m.start(3) + extra.end())))
        # look back at most 160 characters, and never past the previous citation
        lo = max(0, m.start() - 160)
        prev = list(re.finditer(CITE, stmt_text[lo:m.start()]))
        if prev:
            lo += prev[-1].end()
        before = stmt_text[lo:m.start()]
        idents = [x for x in re.findall(r'`([A-Za-z_][\w.\'!?]*)`', before) if not x.endswith('.lean')]
        idents = idents[-len(nums):]
        # identifiers mentioned anywhere in backticked code in that window (for constructions)
        mentioned = [t for span_ in re.findall(r'`([^`]+)`', before)
                     for t in re.findall(r'[A-Za-z_][\w.\'!?]*', span_) if len(t) >= 3]
        src = get(fname)
        if src is None:
            for n, span in nums:
                out.append(dict(kind='prose', what='?', file=fname, cited=n,
                                status=f'{fname} not found next to Statements.lean', correct=None, span=span))
            continue
        if len(idents) < len(nums):
            idents = (idents + [None] * len(nums))[:len(nums)]
        for ident, (n, span) in zip(idents, nums):
            decls = decl_lines(src, ident) if ident else []
            if decls:
                what = f'`{ident}`'
                if any(header_reaches(src, n, d) for d in decls):
                    status, correct = 'ok', n
                elif len(decls) == 1:
                    status, correct = 'stale', decls[0]
                else:
                    status, correct = f'{ident} is declared at several lines {decls}', None
            elif mentioned:
                # a construction, not a named declaration: the cited line must start a declaration
                # whose body uses every identifier the sentence mentions
                what = 'construction using ' + ', '.join(f'`{t}`' for t in mentioned)
                bodies = construction_lines(src, mentioned)
                if n in bodies:
                    status, correct = 'ok', n
                elif len(bodies) == 1:
                    status, correct = 'stale', bodies[0]
                elif bodies:
                    status, correct = f'several declarations use them: lines {bodies}', None
                else:
                    status, correct = 'no declaration uses all of them', None
            else:
                what, status, correct = '(no identifier near the citation)', 'cannot verify', None
            out.append(dict(kind='prose', what=what, file=fname, cited=n,
                            status=status, correct=correct, span=span))
    return out


def lineno(text, pos):
    return text.count('\n', 0, pos) + 1


def main():
    args = [a for a in sys.argv[1:] if not a.startswith('--')]
    fix = '--fix' in sys.argv[1:]
    if len(args) != 1:
        print(__doc__.strip().split('\n\n')[1], file=sys.stderr)
        sys.exit(2)
    path = Path(args[0])
    text = path.read_text(encoding='utf-8')
    get = load_sources(path.parent)
    findings = check(text, get)
    bad = [f for f in findings if f['status'] != 'ok']
    n_d = sum(f['kind'] == 'D-block' for f in findings)
    n_p = len(findings) - n_d
    print(f'citations checked: {n_d} D-block, {n_p} prose; wrong: {len(bad)}')
    for f in bad:
        where = f"Statements.lean:{lineno(text, f['span'][0])}" if f['span'] else ''
        fix_note = f" -> should be {f['file']}:{f['correct']}" if f['correct'] else ''
        print(f"  {where:22s} {f['kind']:7s} {f['what']}: cites {f['file']}:{f['cited']} — {f['status']}{fix_note}")
    if fix:
        fixable = sorted((f for f in bad if f['status'] == 'stale' and f['correct']), key=lambda f: f['span'][0], reverse=True)
        for f in fixable:
            a, b = f['span']
            text = text[:a] + str(f['correct']) + text[b:]
        if fixable:
            path.write_text(text, encoding='utf-8')
            print(f'fixed {len(fixable)} citation(s) in {path}')
        remaining = [f for f in check(text, get) if f['status'] != 'ok']
        if remaining:
            print(f'{len(remaining)} citation(s) need a human:')
            for f in remaining:
                print(f"  Statements.lean:{lineno(text, f['span'][0]) if f['span'] else '?'} {f['what']} — {f['status']}")
        bad = remaining
    print('PASS' if not bad else 'FAIL')
    sys.exit(0 if not bad else 1)


if __name__ == '__main__':
    main()
