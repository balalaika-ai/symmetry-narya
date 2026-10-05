#!/usr/bin/env python3
"""Compile the complete entrypoint from source and preserve diagnostics.

With --dry-run, perform every pre-check (axiom/hole guard, Narya binary present, pinned commits, no uncommitted
edits to tracked files of the vendored checkouts) and print the command, without typechecking or writing evidence/.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import resource
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
BINARY = Path(os.environ.get('NARYA', ROOT / 'vendor/narya/_build/default/bin/narya.exe')).expanduser().resolve()
UPSTREAM_PROOFS = [ROOT / 'vendor/narya/test/black/hott.t' / name for name in ['J.ny', 'univalence.ny']]
COMMAND = [str(BINARY), '-source-only', '-no-reformat', '-v', 'src/all.ny']


def code_only(text, keep_layout=False):
    # Drop comments as Narya's lexer does: nestable block comments {` ... `} and line comments from ` to end of line.
    # With keep_layout, dropped characters become spaces and newlines are kept, so line numbers survive
    # (scripts/audit.py uses this to report file:line).
    out, depth, i = [], 0, 0

    def drop(chunk):
        if keep_layout:
            out.append(''.join('\n' if c == '\n' else ' ' for c in chunk))

    while i < len(text):
        if text.startswith('{`', i):
            drop(text[i:i + 2])
            depth, i = depth + 1, i + 2
        elif depth and text.startswith('`}', i):
            drop(text[i:i + 2])
            depth, i = depth - 1, i + 2
        elif depth:
            drop(text[i])
            i += 1
        elif text[i] == '`':
            j = text.find('\n', i)
            j = len(text) if j < 0 else j
            drop(text[i:j])
            i = j
        else:
            out.append(text[i])
            i += 1
    return ''.join(out)


def source_files():
    return sorted((ROOT / 'src').rglob('*.ny'))


def git(repo, *args):
    return subprocess.check_output(['git', '-C', str(repo), *args], text=True)


def prechecks():
    """Everything that must hold before typechecking; exits with a message on the first failure."""
    if not BINARY.is_file():
        sys.exit(f'Narya executable is absent: {BINARY}; run scripts/bootstrap.sh first.')
    # This guard reports explicit axioms/holes, in our sources and in the two upstream files they export.
    # It is not a consistency or termination checker.
    for p in source_files() + UPSTREAM_PROOFS:
        text = code_only(p.read_text())
        if re.search(r'[?¿ʔ⁇]', text) or re.search(r'\baxiom\b', text):
            sys.exit(f'Explicit axiom or hole in {p.relative_to(ROOT)}')
    pins = json.loads((ROOT / 'upstream.json').read_text())
    for name, spec in pins.items():
        actual = git(ROOT / 'vendor' / name, 'rev-parse', 'HEAD').strip()
        if actual != spec['commit']:
            sys.exit(f'{name}: expected {spec["commit"]}, found {actual}')
    # The pin check above compares commits only; also refuse uncommitted edits to any tracked file of the vendored
    # checkouts: the binary is built from vendor/narya, the proofs export two of its files, and the inventory is
    # extracted from vendor/SymmetryBook. Untracked files are ignored (Narya writes .nyo files next to J.ny and
    # univalence.ny, and dune writes _build/).
    for name in pins:
        dirty = git(ROOT / 'vendor' / name, 'status', '--porcelain', '--untracked-files=no')
        if dirty.strip():
            sys.exit(f'Uncommitted changes to tracked files in vendor/{name}:\n{dirty}')
    for p in UPSTREAM_PROOFS:
        # The exported proof files must be tracked at the pinned commit, not local additions.
        tracked = subprocess.run(['git', '-C', str(ROOT / 'vendor/narya'), 'ls-files', '--error-unmatch',
                                  str(p.relative_to(ROOT / 'vendor/narya'))], capture_output=True)
        if tracked.returncode:
            sys.exit(f'{p.relative_to(ROOT)} is not tracked at the pinned commit')
    return pins


def portable(path):
    # Record paths relative to the repository so the evidence is machine independent.
    try:
        return str(Path(path).resolve().relative_to(ROOT))
    except ValueError:
        return str(path)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--dry-run', action='store_true',
                        help='run all pre-checks and print the command, without typechecking or writing evidence/')
    args = parser.parse_args(argv)
    pins = prechecks()
    if args.dry_run:
        print(f'Pre-checks passed: {len(source_files())} source files and {len(UPSTREAM_PROOFS)} upstream proof files '
              f'free of axioms and holes; binary present; ' +
              ', '.join(f'{name} at {spec["commit"][:12]}' for name, spec in pins.items()) +
              '; no uncommitted edits to tracked vendored files.')
        print('Would run: ' + ' '.join([portable(COMMAND[0])] + COMMAND[1:]))
        return 0
    (ROOT / 'evidence').mkdir(exist_ok=True)
    before = resource.getrusage(resource.RUSAGE_CHILDREN)
    started = time.monotonic()
    with (ROOT / 'evidence/typecheck.log').open('w') as log:
        process = subprocess.Popen(COMMAND, cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        for line in process.stdout:
            log.write(line)
            log.flush()
            print(line, end='', flush=True)
        exit_code = process.wait()
    wall = time.monotonic() - started
    after = resource.getrusage(resource.RUSAGE_CHILDREN)
    # Narya accepts `axiom` with exit code 0 and reports it only as info[I0001]; holes are reported as I3003.
    log_text = (ROOT / 'evidence/typecheck.log').read_text()
    if exit_code == 0 and ('info[I0001]' in log_text or 'info[I3003]' in log_text):
        print('Typechecking assumed an axiom or left a hole (info[I0001]/info[I3003] in the log).', file=sys.stderr)
        exit_code = 1
    # ru_maxrss of RUSAGE_CHILDREN is the largest resident set of any waited-for child; the Narya run dominates the
    # git calls above. It is in bytes on macOS and in KiB on Linux.
    rss_unit = 'bytes' if sys.platform == 'darwin' else 'KiB'
    resources = {
        'wall_seconds': round(wall, 1),
        'user_cpu_seconds': round(after.ru_utime - before.ru_utime, 1),
        'system_cpu_seconds': round(after.ru_stime - before.ru_stime, 1),
        'peak_rss_raw': after.ru_maxrss,
        'peak_rss_raw_unit': rss_unit,
        'peak_rss_bytes': after.ru_maxrss * (1 if rss_unit == 'bytes' else 1024),
        'platform': sys.platform,
        'machine': platform.machine(),
        'source': 'resource.getrusage(RUSAGE_CHILDREN) around the Narya process',
    }
    print(f'Typechecking took {resources["wall_seconds"]} s wall, peak RSS '
          f'{resources["peak_rss_bytes"] / 2 ** 30:.1f} GiB.', file=sys.stderr)
    report = {
        'checked_at_utc': datetime.now(timezone.utc).isoformat(),
        'command': [portable(COMMAND[0])] + COMMAND[1:],
        'exit_code': exit_code,
        'resources': resources,
        'source_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in source_files()},
        'upstream_proof_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                                  for p in UPSTREAM_PROOFS},
        'binary_sha256': hashlib.sha256(BINARY.read_bytes()).hexdigest(),
        'scope': 'Typechecking only. Not proof of full book coverage or foundational consistency.',
        'upstream': pins,
    }
    (ROOT / 'evidence/typecheck.json').write_text(json.dumps(report, indent=2) + '\n')
    return exit_code


if __name__ == '__main__':
    sys.exit(main())
