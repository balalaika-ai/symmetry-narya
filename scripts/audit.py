#!/usr/bin/env python3
"""Lint Narya sources for suspicious recursion, non-positive data types and forbidden constructs.

This scanner recognizes a subset of Narya syntax. A passing run is not a proof of
termination, positivity or consistency. Narya typechecking is a separate check.
"""
import argparse
from collections import Counter
import hashlib
import itertools
import json
import re
import sys

import check

ROOT = check.ROOT
ALLOWLIST = ROOT / 'scripts/audit-allowlist.json'

# Lexer (following vendor/narya/lib/parser/lexer.ml) on comment-free text with the layout preserved.

ONECHAR = {'(': '(', ')': ')', '[': '[', ']': ']', '{': '{', '}': '}', '↦': '↦', '⤇': '⤇', '→': '→', '⇒': '⇒',
           '≔': '≔', '⩴': '⩴', '⩲': '⩲', '…': '…'}
ASCII_SYMBOLS = set('~!@#$%&*/=+|,<>:;-^')
ASCII_OPS = {'->': '→', '=>': '⇒', '|->': '↦', '|=>': '⤇', ':=': '≔', '::=': '⩴', '+=': '⩲', '...': '…'}
HOLE_CHARS = set('?¿ʔ⁇')
SUPER_L, SUPER_R = '⁽', '⁾'
SPECIALS = set(ONECHAR) | ASCII_SYMBOLS | set(' \t\n\r`') | {SUPER_L, SUPER_R} | HOLE_CHARS | {'.', '"'}
RESERVED = {'let', 'rec', 'in', 'axiom', 'def', 'and', 'echo', 'synth', 'quit', 'match', 'return', 'sig', 'data',
            'codata', 'notation', 'import', 'export', 'chdir', 'solve', 'split', 'show', 'display', 'option', 'undo',
            'section', 'fmt', 'end'}
COMMANDS = {'axiom', 'def', 'and', 'echo', 'synth', 'quit', 'notation', 'import', 'export', 'chdir', 'solve',
            'split', 'show', 'display', 'option', 'undo', 'section', 'fmt', 'end'}
ALLOWED_COMMANDS = {'def', 'import', 'export', 'section', 'end', 'notation'}
# Parts of the built-in `calc` notation; they delimit application spines.
NOTATION_WORDS = {'calc', 'by', '∎'}


class Tok:
    __slots__ = ('kind', 'text', 'line')

    def __init__(self, kind, text, line):
        self.kind, self.text, self.line = kind, text, line

    def __repr__(self):
        return f'{self.kind}:{self.text}@{self.line}'


def tokenize(code):
    """Kinds: name (identifier, possibly dotted, e.g. p.2 or eq.eq), con (suc.), field (.fst), sym (one-character
    operators and their ASCII spellings), op (other ASCII symbol runs, including , | :), super, str, hole."""
    toks, i, line, n = [], 0, 1, len(code)
    while i < n:
        c = code[i]
        if c == '\n':
            line += 1
            i += 1
        elif c in ' \t\r':
            i += 1
        elif c in ONECHAR:
            toks.append(Tok('sym', ONECHAR[c], line))
            i += 1
        elif c in ASCII_SYMBOLS:
            j = i
            while j < n and code[j] in ASCII_SYMBOLS:
                j += 1
            word = code[i:j]
            toks.append(Tok('sym', ASCII_OPS[word], line) if word in ASCII_OPS else Tok('op', word, line))
            i = j
        elif c in HOLE_CHARS:
            toks.append(Tok('hole', c, line))
            i += 1
        elif c == SUPER_L:
            j = code.find(SUPER_R, i)
            j = n if j < 0 else j + 1
            toks.append(Tok('super', code[i:j], line))
            i = j
        elif c == SUPER_R:
            toks.append(Tok('super', c, line))
            i += 1
        elif c == '"':
            j = i + 1
            while j < n and code[j] != '"':
                j += 2 if code[j] == '\\' else 1
            toks.append(Tok('str', code[i + 1:j], line))
            line += code.count('\n', i, j)
            i = j + 1
        elif c == '^' and code.startswith('^^(', i):
            j = code.find(')', i)
            toks.append(Tok('super', code[i:j + 1], line))
            i = j + 1
        else:
            # A dotted token: other-words separated by dots, without spaces.
            j = i
            while j < n and (code[j] not in SPECIALS or code[j] == '.'):
                j += 1
            word = code[i:j]
            if word.startswith('.'):
                kind = 'field'
            elif word.endswith('.'):
                kind = 'con'
            else:
                kind = 'name'
            toks.append(Tok(kind, word, line))
            i = j
    return toks


class Group:
    """A bracketed group: kind is '(', '[' or '{'."""
    __slots__ = ('kind', 'items', 'line')

    def __init__(self, kind, items, line):
        self.kind, self.items, self.line = kind, items, line

    def __repr__(self):
        return f'{self.kind}…{"]" if self.kind == "[" else ")" if self.kind == "(" else "}"}@{self.line}'


CLOSE = {'(': ')', '[': ']', '{': '}'}


def nest(toks, where):
    stack = [Group('top', [], 0)]
    for t in toks:
        if t.kind == 'sym' and t.text in CLOSE:
            stack.append(Group(t.text, [], t.line))
        elif t.kind == 'sym' and t.text in (')', ']', '}'):
            g = stack.pop()
            if g.kind == 'top' or CLOSE[g.kind] != t.text:
                raise SystemExit(f'{where}:{t.line}: unbalanced {t.text}')
            stack[-1].items.append(g)
        else:
            stack[-1].items.append(t)
    if len(stack) != 1:
        raise SystemExit(f'{where}:{stack[-1].line}: unclosed {stack[-1].kind}')
    return stack[0].items


def is_tok(item, kind=None, text=None):
    return isinstance(item, Tok) and (kind is None or item.kind == kind) and (text is None or item.text == text)


def is_group(item, kind=None):
    return isinstance(item, Group) and (kind is None or item.kind == kind)


def split_items(items, sep_kind, sep_text):
    # Commas between `match` and its branch group separate scrutinees, not tuple components.
    parts, cur, in_scrutinees = [], [], False
    for it in items:
        if is_tok(it, 'name', 'match'):
            in_scrutinees = True
        elif is_group(it, '['):
            in_scrutinees = False
        if is_tok(it, sep_kind, sep_text) and not (in_scrutinees and sep_text == ','):
            parts.append(cur)
            cur = []
        else:
            cur.append(it)
    parts.append(cur)
    return parts


def flatten(items):
    for it in items:
        if isinstance(it, Group):
            yield from flatten(it.items)
        else:
            yield it


def render(items):
    out = []
    for it in items:
        if isinstance(it, Group):
            out.append(it.kind + render(it.items) + CLOSE[it.kind])
        elif it.kind == 'str':
            out.append(f'"{it.text}"')
        else:
            out.append(it.text)
    s = ' '.join(out)
    s = re.sub(r'([(\[{]) ', r'\1', s)
    s = re.sub(r' ([)\]},])', r'\1', s)
    return s


def first_line(items):
    for t in flatten(items):
        return t.line
    return 0


# Commands and declarations.

class Decl:
    def __init__(self, file, line, kind, items):
        self.file, self.line, self.kind, self.items = file, line, kind, items
        self.name = self.qualified = None
        self.params, self.type_items, self.body = [], [], []
        self.binder_groups = []

    @property
    def where(self):
        return f'{self.file}:{self.line}'

    def digest(self):
        text = self.kind + ' ' + render(self.items)
        return hashlib.sha256(text.encode()).hexdigest()[:16]


def parse_def(d, prefix):
    items = d.items
    if not items or not is_tok(items[0], 'name'):
        d.name = '?'
        return
    d.name = items[0].text
    d.qualified = '.'.join(prefix + [d.name])
    k = 1
    while k < len(items) and not is_tok(items[k], 'sym', '≔'):
        k += 1
    header, d.body = items[1:k], items[k + 1:]
    j = 0
    while j < len(header) and is_group(header[j], '(') and any(is_tok(x, 'op', ':') for x in header[j].items):
        d.binder_groups.append(header[j])
        names, _ = binder_split(header[j])
        d.params.extend(t.text for t in names)
        j += 1
    rest = header[j:]
    if rest and is_tok(rest[0], 'op', ':'):
        d.type_items = rest[1:]
    elif rest:
        d.type_items = rest  # unexpected shape; kept for reporting


def binder_split(group):
    """(x y : T) -> ([x, y], T-items)."""
    items = group.items
    for idx, it in enumerate(items):
        if is_tok(it, 'op', ':'):
            return [t for t in items[:idx] if is_tok(t, 'name')], items[idx + 1:]
    return [], items


def read_sources(sources):
    """sources: (relative path, text) pairs."""
    decls, commands, problems = [], [], []
    for rel, text in sources:
        code = check.code_only(text, keep_layout=True)
        toks = tokenize(code)
        for t in toks:
            if t.kind == 'hole':
                problems.append(('forbidden', rel, t.line, None, f'hole symbol {t.text!r}'))
        items = nest([t for t in toks if t.kind != 'hole'], rel)
        # Split into top-level commands at command keywords (all reserved words in Narya's lexer).
        starts = [k for k, it in enumerate(items) if is_tok(it, 'name') and it.text in COMMANDS]
        if items and (not starts or starts[0] != 0):
            problems.append(('forbidden', rel, first_line(items), None, 'text before the first command'))
        prefix = []
        for a, b in zip(starts, starts[1:] + [len(items)]):
            kw = items[a]
            d = Decl(rel, kw.line, kw.text, items[a + 1:b])
            commands.append(d)
            if kw.text == 'def':
                parse_def(d, prefix)
                decls.append(d)
            elif kw.text == 'section':
                if d.items and is_tok(d.items[0], 'name'):
                    prefix.append(d.items[0].text)
            elif kw.text == 'end':
                if prefix:
                    prefix.pop()
            elif kw.text == 'and':
                parse_def(d, prefix)
                decls.append(d)
    return decls, commands, problems


# (a) Recursion.

class Info:
    """Size information of a term: the argument positions it equals, and for each argument position it is strictly
    smaller than, the depth (number of constructors peeled off that argument to reach it, at least 1)."""
    __slots__ = ('eq', 'lt', 'cube')

    def __init__(self, eq=frozenset(), lt=None, cube=False):
        self.eq, self.lt, self.cube = frozenset(eq), dict(lt or {}), cube


def below(scrut):
    """Depths of the variables bound by a constructor pattern in a match on a term with size information scrut."""
    lt = {p: 1 for p in scrut.eq}
    for p, d in scrut.lt.items():
        lt[p] = max(lt.get(p, 0), d + 1)
    return lt


OPAQUE = Info()


class Walker:
    def __init__(self, decl, qualified_names):
        self.decl = decl
        self.target = decl.name
        self.qualified_names = qualified_names
        self.calls = []          # (line, [Info or None], problem or None)
        self.decls = []          # (keyword, group, env) of data/codata/sig declarations met in the body
        self.let_rec = []

    def lookup(self, text, env):
        if text in env:
            return env[text]
        base, _, rest = text.partition('.')
        if rest and base in env:
            info = env[base]
            if info.cube and rest.isdigit():
                return Info(lt=info.lt)  # a face p.0, p.1, p.2, … of a cube variable bound by a ⤇ pattern
            return OPAQUE
        return None

    def size_of(self, item, env):
        """Size information of a call argument: a variable, or a constructor applied only to variables that lie at
        least two constructors below some argument position (so the application is still strictly below it)."""
        if is_tok(item, 'name'):
            return self.lookup(item.text, env)
        if not is_group(item, '('):
            return None
        inner = unwrap(item.items)
        if len(inner) == 1:
            return self.size_of(inner[0], env)
        if len(inner) < 2 or not is_tok(inner[0], 'con'):
            return None
        infos = [self.size_of(x, env) for x in inner[1:]]
        if any(i is None for i in infos):
            return None
        common = set.intersection(*(set(p for p, d in i.lt.items() if d >= 2) for i in infos))
        return Info(lt={p: min(i.lt[p] for i in infos) - 1 for p in common}) if common else None

    def mentions_target(self, tok, env):
        if tok.kind != 'name':
            return False
        if tok.text in (self.target, self.decl.qualified):
            return tok.text not in env
        base = tok.text.partition('.')[0]
        if base != self.target or base in env:
            return False
        if tok.text != self.target and tok.text in self.qualified_names and tok.text != self.decl.qualified:
            return False  # e.g. `eq.eq`, the constant eq of section eq
        return True

    # A sequence of items forming one expression; head is the next argument position when the sequence is the body
    # of the definition (after its explicit parameters and any lambdas/case trees so far), else None.
    def seq(self, items, env, head):
        i = 0
        while True:
            j = i
            while j < len(items) and is_tok(items[j], 'name') and items[j].text not in RESERVED \
                    and items[j].text not in NOTATION_WORDS and '.' not in items[j].text:
                j += 1
            if j > i and j < len(items) and is_tok(items[j], 'sym') and items[j].text in ('↦', '⤇'):
                env = dict(env)
                for t in items[i:j]:
                    if head is not None:
                        env[t.text] = Info(eq={head})
                        head += 1
                    else:
                        env[t.text] = OPAQUE
                i = j + 1
                continue
            break
        items = items[i:]
        if not items:
            return
        first = items[0]
        if is_tok(first, 'name', 'let'):
            return self.let(items, env, head)
        if is_tok(first, 'name', 'match'):
            return self.match(items, env, head)
        if is_group(first, '[') and head is not None:
            return self.case_tree(first, items[1:], env, head)
        if is_tok(first, 'name') and first.text in ('data', 'codata', 'sig'):
            if len(items) > 1 and isinstance(items[1], Group):
                self.decls.append((first.text, items[1], env))
                return self.expr(items[2:], env)
        self.expr(items, env)

    def let(self, items, env, head):
        k = 1
        if k < len(items) and is_tok(items[k], 'name', 'rec'):
            self.let_rec.append(items[k].line)
            k += 1
        name = items[k].text if k < len(items) and is_tok(items[k], 'name') else None
        k += 1
        depth, eq_at, in_at = 0, None, None
        for m in range(k, len(items)):
            it = items[m]
            if is_tok(it, 'name', 'let'):
                depth += 1
            elif is_tok(it, 'name', 'in'):
                if depth == 0:
                    in_at = m
                    break
                depth -= 1
            elif eq_at is None and depth == 0 and is_tok(it, 'sym', '≔'):
                eq_at = m
        if eq_at is None or in_at is None:
            return self.expr(items[1:], env)
        self.expr(items[k:eq_at], env)
        self.seq(items[eq_at + 1:in_at], env, None)
        env2 = dict(env)
        if name:
            env2[name] = OPAQUE
        self.seq(items[in_at + 1:], env2, head)

    def bind_pattern(self, pat, scrut, cube, env):
        names = [t for t in flatten(pat) if t.kind == 'name' and t.text != '_']
        if any(is_tok(t, 'con') for t in flatten(pat)):
            lt = below(scrut) if scrut else {}
            for t in names:
                env[t.text] = Info(lt=lt, cube=cube)
        elif len(pat) == 1 and names:
            env[names[0].text] = Info(eq=scrut.eq, lt=scrut.lt) if scrut else OPAQUE
        else:
            for t in names:
                env[t.text] = OPAQUE

    def branches(self, group):
        for branch in split_items(group.items, 'op', '|'):
            if not branch:
                continue
            for k, it in enumerate(branch):
                if is_tok(it, 'sym') and it.text in ('↦', '⤇'):
                    yield split_items(branch[:k], 'op', ','), it.text == '⤇', branch[k + 1:]
                    break
            else:
                self.expr(branch, {})

    def match(self, items, env, head):
        k = next((m for m, it in enumerate(items) if is_group(it, '[')), None)
        if k is None:
            return self.expr(items[1:], env)
        scrut_items = items[1:k]
        ret = next((m for m, it in enumerate(scrut_items) if is_tok(it, 'name', 'return')), None)
        if ret is not None:
            self.expr(scrut_items[ret + 1:], env)
            scrut_items = scrut_items[:ret]
        scruts = split_items(scrut_items, 'op', ',')
        infos = []
        for s in scruts:
            self.expr(s, env)
            infos.append(self.lookup(s[0].text, env) if len(s) == 1 and is_tok(s[0], 'name') else None)
        for pats, cube, body in self.branches(items[k]):
            env_b = dict(env)
            for pat, info in zip(pats, infos):
                self.bind_pattern(pat, info, cube, env_b)
            self.seq(body, env_b, head)
        self.expr(items[k + 1:], env)

    def case_tree(self, group, rest, env, head):
        for pats, cube, body in self.branches(group):
            env_b = dict(env)
            if pats and pats[0] and is_tok(pats[0][0], 'field'):
                self.seq(body, env_b, None)  # a comatch (copatterns); its fields add no argument positions
                continue
            for n, pat in enumerate(pats):
                self.bind_pattern(pat, Info(eq={head + n}), cube, env_b)
            self.seq(body, env_b, head + len(pats))
        self.expr(rest, env)

    def group(self, g, env):
        if g.kind == '[':
            for pats, cube, body in self.branches(g):
                env_b = dict(env)
                for pat in pats:
                    self.bind_pattern(pat, None, cube, env_b)
                self.seq(body, env_b, None)
            return
        for part in split_items(g.items, 'op', ','):
            k = next((m for m, it in enumerate(part) if is_tok(it, 'sym', '≔')), None)
            if k is not None and k <= 1:
                part = part[k + 1:]  # field assignment `fld ≔ value` in a tuple
            self.seq(part, env, None)

    def expr(self, items, env):
        k = 0
        while k < len(items):
            it = items[k]
            prev_delim = k == 0 or is_delim(items[k - 1])
            if isinstance(it, Group):
                self.group(it, env)
            elif prev_delim and is_tok(it, 'name') and it.text in ('let', 'match'):
                return self.seq(items[k:], env, None)
            elif prev_delim and is_tok(it, 'name') and binder_run(items, k):
                return self.seq(items[k:], env, None)
            elif is_tok(it, 'name') and it.text in ('data', 'codata', 'sig') and k + 1 < len(items) \
                    and isinstance(items[k + 1], Group):
                self.decls.append((it.text, items[k + 1], env))
                k += 2
                continue
            elif self.mentions_target(it, env):
                problem = None
                if not prev_delim:
                    problem = 'used as an argument (higher-order or partial use)'
                args, m = [], k + 1
                if m < len(items) and is_tok(items[m], 'super'):
                    problem = 'applied under a degeneracy'
                    m += 1
                while m < len(items) and is_arg(items[m]):
                    args.append(self.size_of(items[m], env))
                    m += 1
                if it.text not in (self.target, self.decl.qualified):
                    problem = f'mentioned as {it.text}'
                self.calls.append((it.line, args, problem))
            k += 1


def is_delim(item):
    if isinstance(item, Group):
        return False
    if item.kind in ('sym', 'op'):
        return True
    return item.kind == 'name' and (item.text in RESERVED or item.text in NOTATION_WORDS)


def is_arg(item):
    if isinstance(item, Group):
        return True
    if item.kind in ('con', 'str'):
        return True
    return item.kind == 'name' and item.text not in RESERVED and item.text not in NOTATION_WORDS


def binder_run(items, k):
    j = k
    while j < len(items) and is_tok(items[j], 'name') and items[j].text not in RESERVED and '.' not in items[j].text:
        j += 1
    return j > k and j < len(items) and is_tok(items[j], 'sym') and items[j].text in ('↦', '⤇')


def measure(calls):
    """Find a lexicographic sequence of argument positions that decreases in every call."""
    if not calls or any(problem for _, _, problem in calls):
        return None
    width = max(len(args) for _, args, _ in calls)
    positions = [p for p in range(width) if any(len(a) > p and a[p] and p in a[p].lt for _, a, _ in calls)]

    def decreases(order, args):
        for p in order:
            info = args[p] if len(args) > p else None
            if info is not None and p in info.lt:
                return True
            if info is None or p not in info.eq:
                return False
        return False

    for size in range(1, min(3, len(positions)) + 1):
        for order in itertools.permutations(positions, size):
            if all(decreases(order, args) for _, args, _ in calls):
                return order
    return None


def audit_recursion(decls, qualified_names):
    results = []
    for d in decls:
        if d.kind != 'def' or not d.body:
            continue
        env = {p: Info(eq={n}) for n, p in enumerate(d.params) if p != '_'}
        w = Walker(d, qualified_names)
        w.seq(d.body, env, len(d.params))
        d.walker = w
        mentions_in_decls = any(w.mentions_target(t, {}) for _, g, _ in w.decls for t in flatten([g]))
        if not w.calls and not mentions_in_decls and not w.let_rec:
            continue
        entry = dict(decl=d, calls=w.calls, let_rec=w.let_rec)
        if w.let_rec:
            entry['verdict'], entry['detail'] = 'fail', 'let rec'
        elif not w.calls:
            entry['verdict'], entry['detail'] = 'type', 'self-reference only inside its data/codata/sig declaration'
        else:
            order = measure(w.calls)
            if order is None:
                bad = [f'line {line}: {problem}' for line, _, problem in w.calls if problem]
                entry['verdict'] = 'fail'
                entry['detail'] = 'no decreasing argument recognised' + (f' ({"; ".join(bad)})' if bad else '')
            else:
                names = [param_name(d, p) for p in order]
                entry['verdict'] = 'structural'
                entry['detail'] = ('structural on ' if len(order) == 1 else 'lexicographic on ') + ', '.join(names)
        results.append(entry)
    return results


def param_name(d, p):
    return d.params[p] if p < len(d.params) else f'argument #{p + 1}'


# (b) Positivity.

def occurs(items, names):
    return any(t.kind == 'name' and t.text in names for t in flatten(items))


def unwrap(items):
    while len(items) == 1 and is_group(items[0], '(') and not any(
            is_tok(x, 'op', ':') or is_tok(x, 'op', ',') for x in items[0].items):
        items = items[0].items
    return items


def strictly_positive(items, names):
    """True when `names` occur in the type only as the head of the final codomain of a Π-telescope."""
    items = unwrap(items)
    if not occurs(items, names):
        return True
    pieces = split_items(items, 'sym', '→')
    *domains, codomain = pieces
    for dom in domains:
        if occurs(dom, names):
            return False
    # Binder groups before the codomain: (x : A) (y : B) → C is split as ['(x : A) (y : B)', 'C'].
    codomain = unwrap(codomain)
    if codomain and is_tok(codomain[0], 'name') and codomain[0].text in names:
        return not occurs(codomain[1:], names)
    return False


def audit_positivity(decls):
    found, problems = [], []
    for d in decls:
        w = getattr(d, 'walker', None)
        if w is None:
            continue
        names = {d.name, d.qualified}
        for kw, group, _ in w.decls:
            if kw == 'sig':
                for field in split_items(group.items, 'op', ','):
                    if occurs(field, names):
                        problems.append((d, f'sig field mentions {d.name}: {render(field)}'))
                found.append((d, kw, 'no self-reference' if not occurs([group], names) else 'recursive'))
                continue
            recursive = False
            for ctor in split_items(group.items, 'op', '|'):
                if not ctor:
                    continue
                args, out = [], None
                for k, it in enumerate(ctor):
                    if is_group(it, '('):
                        _, ty = binder_split(it)
                        args.append(ty)
                    elif is_tok(it, 'op', ':'):
                        out = ctor[k + 1:]
                        break
                if kw == 'codata':
                    # x .field : T; the field type must be strictly positive
                    colon = next((k for k, it in enumerate(ctor) if is_tok(it, 'op', ':')), None)
                    args, out = ([ctor[colon + 1:]] if colon is not None else []), None
                if out is not None:
                    pieces = split_items(out, 'sym', '→')
                    *doms, cod = pieces
                    for dom in doms:
                        for b in dom:
                            if is_group(b, '(') and any(is_tok(x, 'op', ':') for x in b.items):
                                args.append(binder_split(b)[1])
                        if not all(is_group(b, '(') for b in dom):
                            args.append(dom)
                    cod = unwrap(cod)
                    if not (cod and is_tok(cod[0], 'name') and cod[0].text in names and not occurs(cod[1:], names)):
                        problems.append((d, f'constructor output type is not {d.name} applied to indices free of '
                                            f'{d.name}: {render(ctor)}'))
                for ty in args:
                    if occurs(ty, names):
                        recursive = True
                        if not strictly_positive(ty, names):
                            problems.append((d, f'{d.name} occurs not strictly positively in {render(ctor)}'))
            found.append((d, kw, 'recursive' if recursive else 'no recursive argument'))
    return found, problems


# (c) Forbidden commands and constructs; import/export targets.

def audit_commands(commands, scanned):
    problems, counts = [], Counter(c.kind for c in commands)
    for c in commands:
        if c.kind not in ALLOWED_COMMANDS:
            problems.append(('forbidden', c.file, c.line, c.name if c.kind == 'and' else None,
                             f'command `{c.kind}`' + (' (mutual definition)' if c.kind == 'and' else '')))
        if c.kind in ('import', 'export') and scanned is not None:
            target = c.items[0].text if c.items and is_tok(c.items[0], 'str') else None
            path = (ROOT / c.file).parent / (target + '.ny') if target else None
            if path is None or path.resolve() not in scanned:
                problems.append(('forbidden', c.file, c.line, None,
                                 f'{c.kind} of {target!r}, which is not among the scanned files'))
    return problems, counts


# (d) Empty-valued declarations.

def result_type(items):
    """The final codomain of a Π-telescope and the number of hypotheses (Π domains; binder groups count per name)."""
    pieces = split_items(unwrap(items), 'sym', '→')
    hyps = 0
    for dom in pieces[:-1]:
        groups = [g for g in dom if is_group(g, '(') and any(is_tok(x, 'op', ':') for x in g.items)]
        hyps += sum(len(binder_split(g)[0]) for g in groups) if groups and len(groups) == len(dom) else 1
    return unwrap(pieces[-1]), hyps


def audit_empty(decls):
    rows, problems = [], []
    for d in decls:
        if not d.type_items:
            continue
        last, hyps = result_type(d.type_items)
        if last and is_tok(last[0], 'name') and (last[0].text == 'Not' or (last[0].text == 'Empty' and len(last) == 1)):
            hyps += len(d.params) + (last[0].text == 'Not')
            rows.append(dict(name=d.qualified, where=d.where, type=render(d.type_items), hypotheses=hyps,
                             closed=not d.params and (last[0].text == 'Empty' and hyps == 0),
                             unconditional=not d.params and hyps == 1))
            if rows[-1]['closed']:
                problems.append(('empty', d.file, d.line, d.qualified, 'closed declaration of type Empty'))
    return rows, problems


# Driver.

def scanned_files():
    return check.source_files() + check.UPSTREAM_PROOFS


def run(sources, scanned):
    decls, commands, problems = read_sources(sources)
    qualified = {d.qualified for d in decls}
    rec = audit_recursion(decls, qualified)
    data_found, pos_problems = audit_positivity(decls)
    cmd_problems, cmd_counts = audit_commands(commands, scanned)
    empty_rows, empty_problems = audit_empty(decls)
    findings = []
    for kind, file, line, name, msg in problems + cmd_problems + empty_problems:
        findings.append(dict(check=kind, name=name, file=file, line=line, message=msg, sha256=None))
    for r in rec:
        if r['verdict'] == 'fail':
            d = r['decl']
            check_name = 'forbidden' if r['let_rec'] else 'recursion'
            findings.append(dict(check=check_name, name=d.qualified, file=d.file, line=d.line, message=r['detail'],
                                 sha256=None if r['let_rec'] else d.digest()))
    for d, msg in pos_problems:
        findings.append(dict(check='positivity', name=d.qualified, file=d.file, line=d.line, message=msg,
                             sha256=d.digest()))
    return dict(decls=decls, commands=commands, rec=rec, data=data_found, pos_problems=pos_problems,
                forbidden=problems + cmd_problems, cmd_counts=cmd_counts, empty=empty_rows, findings=findings)


# Negative and positive controls for the scanner itself: each bad snippet must produce a finding of the named check,
# the good snippets none. `make audit` runs these first.
SELF_TEST_BAD = {
    'loop': ('recursion', 'def loop : Empty ≔ loop'),
    'qualified_loop': ('recursion', 'def S.loop (n : Nat) : Nat ≔ S.loop n'),
    'no_decrease': ('recursion', 'def f (n : Nat) : Empty ≔ f (suc. n)'),
    'wrong_position': ('recursion', 'def g (m n : Nat) : Nat ≔ match m [ zero. ↦ n | suc. k ↦ g n k ]'),
    'mixed_positions': ('recursion', 'def h (m n : Nat) : Nat ≔ match m [ zero. ↦ zero. | suc. a ↦ match n [ '
                                     'zero. ↦ zero. | suc. b ↦ add (h a (suc. n)) (h (suc. m) b) ] ]'),
    'higher_order': ('recursion', 'def k (n : Nat) : Nat ≔ iterate Nat k n zero.'),
    'alias': ('recursion', 'def a (n : Nat) : Nat ≔ let m ≔ n in match m [ zero. ↦ zero. | suc. j ↦ a j ]'),
    'rebuilt': ('recursion', 'def r (n : Nat) : Nat ≔ match n [ zero. ↦ zero. | suc. m ↦ r (suc. m) ]'),
    'rebuilt_mixed': ('recursion', 'def r2 (xs : List Nat) : Nat ≔ match xs [ nil. ↦ zero. | cons. x t ↦ match t '
                                   '[ nil. ↦ zero. | cons. y u ↦ r2 (cons. y t) ] ]'),
    'let_rec': ('forbidden', 'def lr : Empty ≔ let rec f : Empty ≔ f in f'),
    'mutual': ('forbidden', 'def f1 : Empty ≔ g1\nand g1 : Empty ≔ f1'),
    'axiom': ('forbidden', 'axiom ax : Empty'),
    'hole': ('forbidden', 'def x : Nat ≔ ?'),
    'hole_contents': ('forbidden', 'def x : Nat ≔ ¿ zero. ʔ'),
    'hole_numbered': ('forbidden', 'def x : Nat ≔ ⁇0?'),
    'option': ('forbidden', 'option function boundaries ≔ implicit'),
    'echo': ('forbidden', 'echo zero.'),
    'synth': ('forbidden', 'synth zero.'),
    'negative': ('positivity', 'def Bad : Type ≔ data [ bad. (_ : Bad → Empty) ]'),
    'nested': ('positivity', 'def Rose : Type ≔ data [ node. (_ : List Rose) ]'),
    'bad_index': ('positivity', 'def Ix : Type → Type ≔ data [ c. (X : Type) : Ix (Ix X) ]'),
    'recursive_sig': ('positivity', 'def R : Type ≔ sig ( r : R → Empty )'),
    'closed_empty': ('empty', 'def boom : Empty ≔ absurd Empty boom0'),
}
SELF_TEST_GOOD = '''
def Nat : Type ≔ data [ zero. | suc. (_ : Nat) ]
def List (A : Type) : Type ≔ data [ nil. | cons. (_ : A) (_ : List A) ]
def W (A : Type) (B : A → Type) : Type ≔ data [ sup. (a : A) (f : B a → W A B) ]
def eq (A : Type) (a : A) : A → Type ≔ data [ rfl. : eq A a a ]
def add (m n : Nat) : Nat ≔ match n [ zero. ↦ m | suc. k ↦ suc. (add m k) ]
def dbl : Nat → Nat ≔ [ zero. ↦ zero. | suc. k ↦ suc. (suc. (dbl k)) ]
def ack (m n : Nat) : Nat ≔ match m [ zero. ↦ suc. n | suc. p ↦ match n [
  | zero. ↦ ack p (suc. zero.) | suc. q ↦ ack p (ack m q) ] ]
def enc (m n : Nat) (p : Id Nat m n) : Nat ≔ match p [ zero. ⤇ zero. | suc. p ⤇ enc p.0 p.1 p.2 ]
def two (xs ys : List Nat) : Nat ≔ add (match xs, ys [ cons. x xs, cons. y ys ↦ two xs ys | _, _ ↦ zero. ]) zero.
def partial (k : Nat) (A : Type) : Nat ≔ match k [ zero. ↦ zero. | suc. j ↦ iterate Nat (partial j) A ]
def peel (n : Nat) : Nat ≔ match n [ zero. ↦ zero. | suc. m ↦ match m [ zero. ↦ zero. | suc. l ↦ peel (suc. l) ] ]
def S.dec (n : Nat) : Nat ≔ match n [ zero. ↦ zero. | suc. k ↦ S.dec k ]
def nonrec (n : Nat) : Not (Id Nat zero. (suc. n)) ≔ e ↦ nat_encode zero. (suc. n) e
'''


def self_test():
    failures = []
    for name, (expected, text) in SELF_TEST_BAD.items():
        result = run([(f'selftest/{name}.ny', text)], None)
        if not any(f['check'] == expected for f in result['findings']):
            failures.append(f'{name}: expected a {expected} finding, got {result["findings"]}')
    result = run([('selftest/good.ny', SELF_TEST_GOOD)], None)
    if result['findings']:
        failures.append(f'good snippets produced findings: {result["findings"]}')
    kinds = Counter(r['verdict'] for r in result['rec'])
    if kinds != Counter(structural=8, type=4):
        failures.append(f'good snippets: unexpected verdicts {kinds}')
    return failures


def load_allowlist():
    if not ALLOWLIST.exists():
        return []
    data = json.loads(ALLOWLIST.read_text())
    for e in data['entries']:
        for key in ('check', 'name', 'file', 'sha256', 'reason'):
            if not e.get(key):
                raise SystemExit(f'{ALLOWLIST.relative_to(ROOT)}: entry {e} lacks {key!r}')
    return data['entries']


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('-v', '--verbose', action='store_true', help='list every recursive definition and data type')
    args = parser.parse_args(argv)

    broken = self_test()
    if broken:
        print('The audit scanner failed its own controls:', *broken, sep='\n  ', file=sys.stderr)
        return 2

    paths = scanned_files()
    result = run([(str(p.relative_to(ROOT)), p.read_text()) for p in paths], {p.resolve() for p in paths})
    rec, findings = result['rec'], result['findings']

    allow = load_allowlist()
    used, failures, allowed = set(), [], []
    for f in findings:
        n, e = next(((n, e) for n, e in enumerate(allow)
                     if (e['check'], e['name'], e['file']) == (f['check'], f['name'], f['file'])), (None, None))
        if e is not None and f['sha256'] and e['sha256'] == f['sha256']:
            used.add(n)
            allowed.append((f, e))
        else:
            if e is not None:
                f['message'] += (f' [the allowlist entry is for another version of this declaration: re-review it and '
                                 f'set "sha256": "{f["sha256"]}"]')
            failures.append(f)
    stale = [e for n, e in enumerate(allow) if n not in used]

    print(f'Self-test: {len(SELF_TEST_BAD)} bad snippets caught, good snippets accepted.')
    print(f'Scanned {len(paths)} files: {len(result["commands"])} commands ('
          + ', '.join(f'{k} {v}' for k, v in sorted(result['cmd_counts'].items())) + ').')
    verdicts = Counter(r['verdict'] for r in rec)
    n_allowed = Counter(f['check'] for f, _ in allowed)
    print(f'(a) recursion: {len(rec)} declarations mention their own name: {verdicts["structural"]} recognised as '
          f'structural recursion, {verdicts["type"]} only inside their own data declaration, {verdicts["fail"]} not '
          f'recognised ({n_allowed["recursion"]} allowlisted).')
    if args.verbose:
        for r in rec:
            d = r['decl']
            print(f'    {d.where:48} {d.qualified:40} {r["detail"]}')
    recursive_types = sum(1 for _, _, what in result['data'] if what == 'recursive')
    print(f'(b) positivity: {len(result["data"])} data/codata/sig declarations, {recursive_types} recursive, '
          f'{len(result["pos_problems"])} problems ({n_allowed["positivity"]} allowlisted).')
    if args.verbose:
        for d, kw, what in result['data']:
            print(f'    {d.where:48} {d.qualified:40} {kw:7} {what}')
    print(f'(c) forbidden constructs: {len(result["forbidden"])} (axiom, holes, let rec, and, commands other than '
          f'def/import/export/section/end/notation, imports of unscanned files).')
    print(f'Empty-valued declarations: {len(result["empty"])}; '
          f'closed Empty: {sum(r["closed"] for r in result["empty"])}.')
    if allowed:
        print(f'Allowlisted ({len(allowed)}, see {ALLOWLIST.relative_to(ROOT)}):')
        for f, e in allowed:
            print(f'    {f["check"]:10} {f["file"]}:{f["line"]} {f["name"]}')
    for e in stale:
        print(f'warning: unused allowlist entry {e["check"]} {e["name"]} ({e["file"]}, sha256 {e["sha256"]})')

    if failures:
        print(f'\n{len(failures)} audit failures:', file=sys.stderr)
        for f in failures:
            digest = f' (sha256 {f["sha256"]})' if f['sha256'] else ''
            print(f'  {f["check"]}: {f["file"]}:{f["line"]} {f["name"] or ""}: {f["message"]}{digest}',
                  file=sys.stderr)
        return 1
    print('Source lint passed (heuristic checks only).')
    return 0


if __name__ == '__main__':
    sys.exit(main())
