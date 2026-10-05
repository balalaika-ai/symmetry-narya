#!/usr/bin/env python3
"""Typecheck the files of the blind statement check (chapters/*/blind/*.ny) and write evidence/blind.json.

Different chapters use the same names, so each Narya run loads the files of one chapter only. For each chapter,
one run checks from source all leaf files of the folder (files that no other file of the folder imports); the
leaves import all the other files. The blind files import the modules through ../../../src. Narya does not reduce
`..` in paths, so a compiled module could load its imports a second time through a different path; thus each run
uses -source-only. Each run works in its own copy of src/ and of the folder, so parallel runs share no files.
Chapter 10 is the exception: its leaves together need more than 100 GB of memory, so each of its leaves gets its
own run. With --jobs N, up to N runs are active at the same time.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor
import json
import re
import shutil
import subprocess
import time
from pathlib import Path

import check

ROOT = check.ROOT
IMPORT = re.compile(r'^\s*(?:import|export)\s+"([^"]+)"', re.M)
SEPARATE = {'ch10'}  # chapters whose leaves are checked in separate runs


def leaves(folder):
    files = sorted(folder.glob('*.ny'))
    imported = {name for f in files for name in IMPORT.findall(f.read_text())}
    return [f for f in files if f.stem not in imported]


def check_run(folder, files):
    """Check the given leaf files of one chapter folder from source in a fresh copy of src/ and of the folder."""
    chapter = folder.parent.name
    run_root = ROOT / '.blind-runs' / f'{chapter}-{Path(files[0]).stem}'
    shutil.rmtree(run_root, ignore_errors=True)
    (run_root / 'chapters' / chapter / 'blind').mkdir(parents=True)
    (run_root / 'src').mkdir()
    for f in (ROOT / 'src').glob('*.ny'):
        shutil.copy2(f, run_root / 'src' / f.name)
    for f in folder.glob('*.ny'):
        shutil.copy2(f, run_root / 'chapters' / chapter / 'blind' / f.name)
    (run_root / 'vendor').symlink_to((ROOT / 'vendor').resolve())
    start = time.time()
    try:
        run = subprocess.run([str(check.BINARY), '-source-only', '-no-reformat', *files], cwd=run_root, text=True,
                             stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    finally:
        shutil.rmtree(run_root, ignore_errors=True)
    bad = re.search(r'error\[|bug\[|info\[I0001\]|info\[I3003\]', run.stdout)
    result = {'chapter': chapter, 'leaves': files, 'exit_code': run.returncode,
              'passed': run.returncode == 0 and not bad, 'wall_seconds': round(time.time() - start, 1)}
    if not result['passed']:
        result['output'] = run.stdout[-4000:].replace(str(run_root) + '/', '')
    print(f"{chapter} ({len(files)} leaves): {'ok' if result['passed'] else 'FAILED'} "
          f"({result['wall_seconds']} s)", flush=True)
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--jobs', type=int, default=1)
    parser.add_argument('chapters', nargs='*', help='chapter folders, for example ch04 (default: all)')
    args = parser.parse_args()
    check.prechecks()
    folders = sorted(p for p in (ROOT / 'chapters').glob('*/blind')
                     if p.is_dir() and (not args.chapters or p.parent.name in args.chapters))
    runs = []
    for folder in folders:
        files = [f'chapters/{folder.parent.name}/blind/{leaf.name}' for leaf in leaves(folder)]
        runs += [(folder, [f]) for f in files] if folder.parent.name in SEPARATE else [(folder, files)]
    with ThreadPoolExecutor(args.jobs) as pool:
        results = list(pool.map(lambda r: check_run(*r), runs))
    for r in results:
        r['files'] = len(list((ROOT / 'chapters' / r['chapter'] / 'blind').glob('*.ny')))
    (ROOT / 'evidence').mkdir(exist_ok=True)
    (ROOT / 'evidence/blind.json').write_text(json.dumps(results, indent=2) + '\n')
    failed = [r['chapter'] for r in results if not r['passed']]
    print(f'{len(results) - len(failed)} of {len(results)} runs pass.')
    raise SystemExit(1 if failed else 0)


if __name__ == '__main__':
    main()
