# Universe notes

The pinned Narya has one universe, `Type : Type`. The book uses a hierarchy of univalent universes. Nobody has
ported this development to a stratified theory or checked it there. This page lists the points that such a port
must solve.

## Propositional truncation

`Mere A` in [module 29](../src/29-propositional-truncation.ny) is

```text
(P : Type) → isProp P → (A → P) → P
```

With a universe `Uᵢ`, the quantifier over `P : Uᵢ` puts this encoding in `Uᵢ₊₁`. Thus the encoding does not give
the propositional truncation of the book, which stays in the same universe. A stratified version needs a
primitive truncation or resizing assumptions. These must include elimination into the propositions that the
proofs use.

## Large types and the circle

`SetTypes = Σ Type isSet`, the types of permutations and cycles, and their components are in a universe above the
universe of their carriers in a stratified theory. The constructed circle is a component of `Cycles`. If the
formalization stores this component in `CircleSignature.carrier : Type`, its level stays unsolved.

[Module 283](../src/283-circle-universe-smallness.ny) proves essential smallness under replacement in the model
of smallness predicates. This is a theorem in the single universe of Narya. It is not a checked universe
assignment for the construction.

The signatures for the circle, the truncations and the quotients quantify over target types or families. A port
must give explicit levels to these quantifiers. It must also check which elimination levels each construction
supports.

## Universe models

[Module 190](../src/190-universes.ny) represents a universe by a smallness predicate with values in propositions,
and by closure properties. `total_universe`, `total_nested` and `total_replacement` use the single universe to
make every type small. Their literal instances for the universe itself have no direct equivalent in a hierarchy
`U₀ : U₁ : …`.

The general theorems take a model universe as a parameter. Resizing and replacement are hypotheses.
`book-inventory.json` records where a proof uses them. Universe identities and transport (`Id Type A B`, `ua`,
`transport Type`) also need explicit levels in a port. The source lint does not find or check these levels.
