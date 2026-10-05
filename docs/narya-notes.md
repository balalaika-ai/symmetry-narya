# Narya notes

These notes apply to the pinned commit `efafad2` in the default HOTT mode.

## Record projections at higher dimensions

Some record projections at higher dimensions cause the error
`bug[E0500]: dimension mismatch in field of struct`. The reproducers in [tests/narya](../tests/narya) do not
need other files:

| File | Expected result |
|---|---|
| `e0500-minimal.ny` | E0500 on a projection from a transported degenerated tuple |
| `e0500-concat-p1-sigma.ny` | E0500 when the projected right unit law is compared with the base law |
| `e0500-truncation-step.ny` | E0500 with an inline base case for path induction |
| `e0500-truncation-step-workaround.ny` | The check passes when the base case is a separate definition |

To run a reproducer, use this command:

```sh
vendor/narya/_build/default/bin/narya.exe -source-only -no-reformat tests/narya/e0500-minimal.ny
```

The reproducers are not part of the proofs. The minimal example uses axioms only to show the error.

The formalization avoids the error in three places:

- Module 186 evaluates fiber points through `.trl`.
- Module 201 puts the base case of path induction in a separate definition.
- Module 281 proves the laws for paths over paths directly over the base laws. It does not compare projected
  two-dimensional paths.

## Compiled files

Narya writes `.nyo` files next to the loaded sources, also with `-source-only`. This flag makes Narya load the
sources. It does not stop the output of compiled files. Thus, do not run two checks of the same source tree at
the same time. `-no-reformat` stops Narya from a change to the input file on the command line.

Instances of the constructed circle have explicit types. Without a type annotation, a definition can store a
large normalized type in the compiled file.

## Import paths with `..`

Narya resolves an import relative to the directory of the importing file. It does not reduce `..` in the result.
Thus, a file that two modules import through different relative paths loads two times. The two copies define
different constants with the same names, and their types do not agree.

The reproducer is in [tests/narya/dotdot](../tests/narya/dotdot):

```sh
vendor/narya/_build/default/bin/narya.exe -source-only -v tests/narya/dotdot/a/top.ny
```

The output shows that `a/base.ny` loads two times. The second time, its path is `a/../b/../a/base.ny`. Then the
check of `a/top.ny` fails, because the two copies of `E` are different types.

For this reason, all modules of this repository are in one directory, `src/`.

## Anomaly `Meta.Map.find_opt`

Some runs stop with `bug[E0000]: anomaly: failure: Meta.Map.find_opt`. The message gives no location. The
blind statement files (`chapters/*/blind/`) import modules through `../../../src`. When Narya loads the compiled
files of these modules, some runs stop with this anomaly. With `-source-only`, the same files pass. Thus
`make blind` uses `-source-only`. There is no minimal reproducer yet.
