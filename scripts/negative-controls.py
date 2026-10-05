#!/usr/bin/env python3
"""Check that Narya rejects two specific false reflexivity proofs."""
import json
import os
from pathlib import Path
import subprocess
import tempfile

import check

root = check.ROOT
binary = check.BINARY
check.prechecks()
cases = {
    'zero_is_one': 'def false_claim : Id Nat zero. (suc. zero.) ≔ refl (zero. : Nat)',
    'successor_transport_is_identity': 'def false_claim : Id Int (int_universe_loop .trr int_zero) int_zero ≔ refl int_zero',
}
results = {}
with tempfile.TemporaryDirectory(prefix='negative-controls-', dir=root) as work:
    for name, source in cases.items():
        path = Path(work) / (name + '.ny')
        path.write_text('import "../src/03-integers"\n' + source + '\n')
        result = subprocess.run([str(binary), '-source-only', '-no-reformat', str(path)],
                                cwd=root, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        # A parse failure or missing import is not evidence of rejecting the claim.
        rejected = result.returncode == 1 and 'error[E0401]' in result.stdout and 'unequal constructors' in result.stdout
        # Strip the checkout location so the recorded evidence is machine independent.
        output = result.stdout.replace(str(work) + os.sep, '').replace(str(root) + os.sep, '')
        results[name] = {'statement': source, 'exit_code': result.returncode,
                         'rejected_with_type_mismatch': rejected, 'output': output}
(root / 'evidence/negative-controls.json').write_text(json.dumps(results, indent=2, ensure_ascii=False) + '\n')
for name, result in results.items():
    print(f'{name}: ' + ('rejected as expected' if result['rejected_with_type_mismatch'] else 'UNEXPECTED RESULT'))
raise SystemExit(0 if all(r['rejected_with_type_mismatch'] for r in results.values()) else 1)
