#!/bin/sh
set -eu
cd "$(dirname "$0")/.."
python3 - <<'PY'
import json, subprocess
from pathlib import Path
for name, spec in json.loads(Path('upstream.json').read_text()).items():
    dest = Path('vendor') / name
    if not dest.exists():
        subprocess.run(['git', 'clone', spec['url'], str(dest)], check=True)
        subprocess.run(['git', '-C', str(dest), 'checkout', '--detach', spec['commit']], check=True)
    actual = subprocess.check_output(['git', '-C', str(dest), 'rev-parse', 'HEAD'], text=True).strip()
    if actual != spec['commit']:
        raise SystemExit(f'{dest}: expected {spec["commit"]}, found {actual}; not overwriting')
PY
if ! opam switch list --short | grep -qx symmetry-narya; then
    opam switch create symmetry-narya ocaml-base-compiler.5.3.0 --no-switch -y
fi
opam install --switch=symmetry-narya dune -y
cd vendor/narya
opam exec --switch=symmetry-narya -- dune build narya.opam
opam install --switch=symmetry-narya . --deps-only -y
opam exec --switch=symmetry-narya -- dune build bin/narya.exe
