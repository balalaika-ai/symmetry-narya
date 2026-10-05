#!/usr/bin/env python3
"""Inventory source obligations; no declaration of completion is inferred."""
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
KINDS = 'definition|lemma|theorem|corollary|conjecture|axiom|construction|principle|xca|exercise|example|remark'
# Book order (book.tex); the appendices are lettered.
CHAPTERS = [(2, 'intro-uf.tex'), (3, 'circle.tex'), (4, 'group.tex'), (5, 'actions.tex'), (6, 'cats.tex'),
            (7, 'absgroup.tex'), (8, 'congp.tex'), (9, 'subgroups.tex'), (10, 'fingp.tex'), (11, 'fggroups.tex'),
            (12, 'abelian.tex'), (13, 'fields.tex'), (14, 'geometry.tex'), (15, 'galois.tex'), ('A', 'history.tex'),
            ('B', 'metamath.tex')]
rows = []


def extract(chapter, filename, section, ordinal):
    """Append the blocks of one source file; \\input files are read in place (their blocks keep their own source)."""
    source = (ROOT / 'vendor/SymmetryBook' / filename).read_text()
    # TeX comments are discarded but line numbers are preserved.
    source = re.sub(r'(?<!\\)%[^\n]*', '', source)
    for m in re.finditer(r'\\section\{([^\n]*)|\\begin\{(' + KINDS + r')\}|\\input\{([^}]+)\}', source):
        if m.group(1) is not None:
            section = m.group(1)
            continue
        if m.group(3) is not None:
            section, ordinal = extract(chapter, m.group(3) + '.tex', section, ordinal)
            continue
        ordinal += 1
        kind = m.group(2)
        end = source.find('\\end{' + kind + '}', m.end())
        body = source[m.end():end] if end >= 0 else source[m.end():]
        labels = re.findall(r'\\label\{([^}]+)\}', body)
        rows.append(dict(chapter=chapter, ordinal=ordinal, kind=kind,
                         source=filename, line=source.count('\n', 0, m.start()) + 1,
                         section_raw=section, labels=labels,
                         status='unmapped', declarations=[]))
    return section, ordinal


for chapter, filename in CHAPTERS:
    extract(chapter, filename, '', 0)
output = ROOT / 'book-inventory.json'


if output.exists():
    previous = json.loads(output.read_text())
    by_labels = {}
    for r in previous:
        if r['labels']:
            by_labels.setdefault((r['source'], tuple(r['labels'])), []).append(r)
    by_line = {(r['source'], r['line'], r['section_raw'], r['kind']): r
               for r in previous if not r['labels']}
    for row in rows:
        prev = None
        if row['labels']:
            candidates = by_labels.get((row['source'], tuple(row['labels'])), [])
            prev = candidates[0] if len(candidates) == 1 else None
        if not row['labels']:
            prev = by_line.get((row['source'], row['line'], row['section_raw'], row['kind']))
        if prev is not None:
            # Keep everything that is not re-extracted from the book: status, principal, declarations, note.
            for key, value in prev.items():
                if key not in ('chapter', 'ordinal', 'kind', 'source', 'line', 'section_raw', 'labels'):
                    row[key] = value
output.write_text(json.dumps(rows, ensure_ascii=False, indent=2) + '\n')
for chapter, _ in CHAPTERS:
    subset = [r for r in rows if r['chapter'] == chapter]
    print(f'Chapter {chapter}: {len(subset)} source blocks; ' +
          f'{sum(r["status"] == "unmapped" for r in subset)} unmapped')
