# Symmetry in Narya

This repository is a formalization of the book
[*Symmetry*](https://github.com/UniMath/SymmetryBook) by Bezem, Buchholtz, Cagne, Dundas and Grayson.
It uses the proof assistant [Narya](https://github.com/gwaithimirdain/narya) in its default HOTT mode.
The table below shows the chapters that it covers.

## Chapters

Each chapter has a folder in [`chapters/`](chapters). The README of the folder gives the status of the chapter,
the open gaps and the corrections to the book. It also links each block of the book to its principal declarations.

<!-- chapter-table:begin -->
| Chapter | Blocks | Mapped | Refuted | Partial | Informal | Blind check gaps | Open gaps |
|---|---:|---:|---:|---:|---:|---|---:|
| [Chapter 2: An introduction to univalent mathematics](chapters/ch02/README.md) | 196 | 196 | 0 | 0 | 0 | — | 2 |
| [Chapter 3: The universal symmetry: the circle](chapters/ch03/README.md) | 102 | 101 | 1 | 0 | 0 | — | 10 |
| [Chapter 4: Groups, concretely](chapters/ch04/README.md) | 95 | 92 | 3 | 0 | 0 | 0 | 8 |
| [Chapter 5: Actions](chapters/ch05/README.md) | 112 | 110 | 1 | 0 | 1 | 0 | 11 |
| [Chapter 6: A categorical interlude](chapters/ch06/README.md) | 89 | 89 | 0 | 0 | 0 | 0 | 10 |
| **Total** | **594** | **588** | **5** | **0** | **1** | | **41** |
<!-- chapter-table:end -->

The columns have these meanings:

- **Blocks**: the definitions, lemmas, theorems, constructions, exercises, examples and remarks of the book.
- **Mapped**: the block has a formal statement and a proof.
- **Refuted**: the block is false as printed. The repository proves a counterexample and a corrected statement.
- **Partial**: the repository formalizes only a part of the block.
- **Informal**: the block has no mathematical claim, for example a historical comment.
- **Blind check gaps**: the number of gaps in the blind statement check. A dash shows that the chapter has no
  blind check. Refer to [Blind statement check](#blind-statement-check).
- **Open gaps**: partial blocks, gaps of the blind statement check, and claims of the running text that are not
  formalized or only partly formalized.

The mappings need mathematical review. A successful typecheck does not show that a formal statement agrees with
the book. [`book-inventory.json`](book-inventory.json) has a note for each block. The note gives every difference
between the formal statement and the printed text.

## Contents

| Path | Contents |
|---|---|
| [`src/`](src) | The Narya modules. [`src/all.ny`](src/all.ny) exports all modules. |
| [`chapters/`](chapters) | One folder for each chapter: the status page and the files of the blind statement check. |
| [`book-inventory.json`](book-inventory.json) | All blocks of the book, with status, declarations and notes. |
| [`text-claims.json`](text-claims.json) | The claims of the running text and of the footnotes. |
| [`docs/`](docs) | Notes on the book, on Narya and on universes. |
| [`tests/narya/`](tests/narya) | Reproducers of Narya errors. |
| [`scripts/`](scripts) | The checks and the generators. |
| [`evidence/`](evidence) | The results of the last full check. |

The number of a module shows its chapter:

| Modules | Chapter |
|---|---|
| 00–289 | 2 and 3 |
| 400–499, 500–599, …, 1500–1599 | 4, 5, …, 15 |
| 1700–1799 | Appendix B |

All modules are in one directory. The pinned Narya does not reduce `..` in import paths. Two modules can import
the same file through different relative paths. Then Narya loads the file two times and gets two copies of its
types. Refer to [Narya notes](docs/narya-notes.md).

## Build and check

You must have `git`, `python3`, `opam`, a C toolchain, GMP and `pkg-config`. If opam has no configuration, run
`opam init --bare --no-setup`.

```sh
./scripts/bootstrap.sh  # get the pinned upstreams and build Narya with OCaml 5.3.0
make check              # typecheck src/all.ny from source and write evidence/typecheck.json
make blind              # typecheck the files of the blind statement check
make controls           # make sure that Narya rejects two false proofs
make audit              # heuristic lint for recursion, positivity and forbidden constructs
make index-check        # make sure that the chapter pages and the chapter table are up to date
make inventory          # extract the book blocks again and keep their mappings
```

The last full check (`make check`) took 2 h 19 min and 27 GB of memory on an x86_64 Linux server. Narya
uses one processor core. In `make blind`, the longest run (chapter 13) took 41 min.

[`upstream.json`](upstream.json) pins Narya and SymmetryBook. `scripts/bootstrap.sh` uses an existing checkout
only if its commit is the pinned commit. `make check` does these steps:

1. It makes sure that the tracked files of the two checkouts have no changes.
2. It rejects axioms and holes in the proof sources.
3. It reads the diagnostics of Narya and rejects assumed axioms and unsolved holes.

To use a different Narya executable, set `NARYA=/path/to/narya.exe`.

[`evidence/typecheck.json`](evidence/typecheck.json) records the hashes of the sources, of the upstream proofs and
of the executable. It also records the command, the result, the time and the memory. The diagnostics go to
`evidence/typecheck.log`, which git ignores. [`evidence/negative-controls.json`](evidence/negative-controls.json)
records the negative controls and [`evidence/blind.json`](evidence/blind.json) the blind statement check.

## Blind statement check

The main risk of a formalization is a formal statement that does not say what the book says. For chapters 4 to 15
and appendix B, we wrote a second set of statements from the book text only. We did not use the formal code of the
chapter for this. These statements are in `chapters/<chapter>/blind/`.

Then the bridge files of the same folder derive each blind statement from the main declarations. Each block gets
one of these results:

- **bridged**: the blind statement follows from the main declarations.
- **bridged-corrected**: the literal blind statement is false. The bridge file proves a counterexample. The
  corrected blind statement follows from the main declarations.
- **gap**: the blind statement does not follow. The note gives the reason.
- **no-claim**: the block has no mathematical claim.

`chapters/<chapter>/blind/bridges.json` records the result for each block. The check found statements that were
weaker than the book. These statements are now corrected. The chapters 2, 3 and 11 do not have a blind check.

The blind files of different chapters use the same names. Thus, a Narya run loads the files of one chapter only.
For each chapter, `make blind` checks from source the files that no other file of the folder imports. These files
import all the other files.

## Foundations

The proofs use the native `Id`, transport and univalence of Narya. `src/00-foundations.ny` exports `J.ny` and
`univalence.ny` from the pinned Narya test suite. Module 20 proves the two inverse laws of univalence.
Module 11 introduces the conventions of the book for the orientation of paths and for contractibility.

The pinned Narya has no higher inductive types. Thus, a signature record specifies each higher inductive type
of the book with its induction and computation laws. Examples are `CircleSignature` and `TruncationSignature`.
General results take these records as parameters. Where the book needs a specific object, the repository
constructs it:

- Propositional truncation is the impredicative encoding `Mere` (module 29).
- The circle is the component of the infinite cycle `(Int, succ)` in the type of cycles (modules 220–223).
  Modules 224, 250 and 251 apply the results about the circle to this construction.
- Quotients and higher truncations are images of relations.

Smallness predicates model the universes of the book (modules 190–193). Resizing, replacement and classical
principles are explicit hypotheses where a proof uses them.

The path eliminator `J` of Narya has a propositional computation rule. Where the book uses a definitional
computation rule, the inventory names the proved identification that the formalization uses.

| Level n in the book | Index of `HLevel` | Native truncation |
|---|---:|---|
| −2 (contractible) | 0 | `MinusTwoTrunc` (= Unit) |
| −1 (proposition) | 1 | `Trunc 0` = `Mere` |
| 0 (set) | 2 | `Trunc 1` (equivalent to `SetTrunc`) |

## Limits of verification

The pinned Narya has `Type : Type`. It has no checker for termination, positivity or productivity. Its
documentation says that the universe is inconsistent. Thus, a successful typecheck is not a consistency result.

`make audit` is a heuristic scanner for a subset of the Narya syntax. It finds unrecognized recursion,
non-positive datatypes, forbidden commands, imports outside the scanned sources and closed declarations of
`Empty`. It has one exception, bound to a hash, for guarded corecursion in the upstream proofs. A pass of this
lint does not prove termination, positivity or soundness.

[Universe notes](docs/impredicativity.md) describe the main uses of the single universe and the obstacles to a
stratified version. Nobody has checked such a version. [Narya notes](docs/narya-notes.md) describe the
workarounds for Narya errors and link to their reproducers. [Book notes](docs/book-notes.md) describe the
corrections to chapters 2 and 3.

## Contributing

1. Add a module to `src/` with a number in the range of its chapter. Export it from `src/all.ny`.
2. Give each declaration a name that no other module uses.
3. Give an explicit type to each top-level definition, especially for instances of the constructed circle.
4. Update the mappings in `book-inventory.json` and the claims in `text-claims.json`.
5. Run `make index`, and then the checks above. A new extraction of the inventory must keep the mappings.

## License

The license is [GPL-3.0-or-later](LICENSE). The imported Narya proofs are by Michael Shulman and use the same
license. Maintained by [balalaika.ai](https://github.com/balalaika-ai).
