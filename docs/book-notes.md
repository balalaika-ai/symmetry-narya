# Book notes

The references are to the SymmetryBook commit `c0c6ab3`, which `upstream.json` pins. The inventory records how each
formal statement is different from the printed text.

## Surjection cancellation

`xca:cancel-surjection` (`circle.tex:3104`) says that a surjection `p : A → B` gives an equivalence
`(f = g) → (f ∘ p = g ∘ p)` for all `Y` and `f, g : B → Y`. This is not true unless the target has an
additional restriction.

For example, let `A = Unit` and `B = Y = S¹`, and let `p` select the base point. The circle is connected, so
`p` is surjective. The identity map and the constant map agree after precomposition with `p`. If the two maps
were equal, the circle would be contractible. But the loop space of the circle is equivalent to the integers.

[Module 40](../src/40-map-cancellation.ny) gives counterexamples with the groupoid of two-element sets and with
`Type`. It proves `cancel_surjection_into_set` for targets that are sets. `cancel_n_connected` in
[module 285](../src/285-chapter-three-completions.ny) is more general: it uses an n-connected map and a target
that is an (n+1)-type.

## Cycle conventions

- After `lem:deg-m-on-Cyc` (`circle.tex:2844`), the symmetry of the root cycle is the inverse of the root
  permutation, `(√[m]t)⁻¹`. The root of `t⁻¹` is a different operation. Modules 137 and 262 use the first one.
- `con:psi-alpha-m` prints `α_m` in the orientation opposite to its construction (`circle.tex:1921,1962`).
  [Module 282](../src/282-explicit-power-degree.ny) follows the construction and states its maps explicitly.
- The count of generators in `rem:thenonuniquenessofgeneratorsofmodulararithmetic1` (`circle.tex:2233`) needs
  a separate case for `m = 1`: the identity generates that cycle. Modules 241 and 242 include this case.
- Module 285 has separate cases `k = 0,1` for the count of k-cycles. Module 286 proves the comparison between
  the list notation and the injective enumerations for `k ≥ 2`.

`book-inventory.json` records the other differences next to their mappings. These include the computation rules
that the formalization replaces with propositional identifications.
