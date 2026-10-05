export "529-burnside-chain"

{` Chapter 5, lem:burnside, eq:burnside: for a finite group G and a finite
   G-set X, Card(Σ_{g : USym G} X^g) = Card(X/G) × Card(G).

   As in the book, the statement is a proposition, so the per-orbit data
   (x_O, f_O) of the Lagrange construction may be chosen. The book picks
   the `least' x_O and g via enumerations of X(sh_G) and USym G; here the
   same data are obtained by finite choice (module 34) over the finite set
   X/G, with x_O from the transitivity of X_O and f_O from
   lagrange_choice_merely (finite choice over X_O(sh_G)). No classical
   principle is used. `}

{` O(sh_G, x) is decidable, as O = [x] is (X/G is finite, hence has
   decidable equality). `}
def burnside_orbit_member_decidable (G : Group) (hG : IsFiniteGroup G) (X : GSet G) (hX : IsFiniteGSet G X)
  (O : Orbits G X) (x : gset_underlying G X) : Decidable (OrbitMember G X O (shape G, x))
  ≔ match finite_decidable_equality (Orbits G X) (burnside_orbits_finite G hG X hX) O (orbit_of_point G X x) [
    | inl. p ↦ inl. (orbit_member_of_path G X O (shape G, x) p)
    | inr. np ↦ inr. (m ↦ np (orbit_path_of_member G X O (shape G, x) m)) ]

{` The underlying set X_O(sh_G) of an orbit is finite. `}
def burnside_orbit_underlying_finite (G : Group) (hG : IsFiniteGroup G) (X : GSet G) (hX : IsFiniteGSet G X)
  (O : Orbits G X) : IsFiniteGSet G (gsubset_gset G X (O .fst))
  ≔ finite_decidable_subset (gset_underlying G X) hX (x ↦ OrbitMember G X O (shape G, x))
      (x ↦ orbit_member_prop G X O (shape G, x)) (x ↦ burnside_orbit_member_decidable G hG X hX O x)

{` Every orbit merely has the data (x_O, f_O). `}
def burnside_orbit_choice_merely (G : Group) (hG : IsFiniteGroup G) (X : GSet G) (hX : IsFiniteGSet G X)
  (O : Orbits G X) : Mere (BurnsideOrbitChoice G X O)
  ≔ let Y ≔ gsubset_gset G X (O .fst) in
    let Ys ≔ gset_underlying G Y in
    let C ≔ BurnsideOrbitChoice G X O in
    mere_rec Ys (Mere C) (mere_isprop C)
      (xO ↦ mere_rec (LagrangeChoice G Y xO) (Mere C) (mere_isprop C) (f ↦ mere C (xO, f))
        (lagrange_choice_merely G Y xO (O .snd) (burnside_orbit_underlying_finite G hG X hX O)))
      (orbit_has_base_member G X O)

def burnside_orbit_sum_finite (G : Group) (hG : IsFiniteGroup G) (X : GSet G) (hX : IsFiniteGSet G X)
  : IsFinite (BurnsideOrbitSum G X)
  ≔ finite_of_equiv (BurnsideOrbitSum G X) (BurnsideSum G X)
      (canonical_inverse_equiv (BurnsideSum G X) (BurnsideOrbitSum G X) (burnside_chain_equiv G X))
      (burnside_sum_finite G hG X hX)

{` lem:burnside, eq:burnside. `}
def burnside_lemma (G : Group) (hG : IsFiniteGroup G) (X : GSet G) (hX : IsFiniteGSet G X)
  : Id Nat (cardinality (BurnsideSum G X) (burnside_sum_finite G hG X hX))
      (mul (cardinality (Orbits G X) (burnside_orbits_finite G hG X hX)) (group_card G hG))
  ≔ let Or ≔ Orbits G X in
    let hOr ≔ burnside_orbits_finite G hG X hX in
    let hS ≔ burnside_sum_finite G hG X hX in
    let hT ≔ burnside_orbit_sum_finite G hG X hX in
    let F ≔ (O ↦ Σ (gset_underlying G (gsubset_gset G X (O .fst))) (y ↦ USym (stabilizer_group G X (y .fst))))
      : Or → Type in
    let Goal ≔ Id Nat (cardinality (BurnsideSum G X) hS) (mul (cardinality Or hOr) (group_card G hG)) in
    mere_rec ((O : Or) → BurnsideOrbitChoice G X O) Goal
      (nat_set (cardinality (BurnsideSum G X) hS) (mul (cardinality Or hOr) (group_card G hG)))
      (cs ↦ concat Nat (cardinality (BurnsideSum G X) hS) (cardinality (BurnsideOrbitSum G X) hT)
        (mul (cardinality Or hOr) (group_card G hG))
        (cardinality_equiv (BurnsideSum G X) (BurnsideOrbitSum G X) (burnside_chain_equiv G X) hS hT)
        (cardinality_equinumerous_sum Or (USym G) F hOr hG
          (O ↦ canonical_inverse_equiv (USym G) (F O) (burnside_orbit_lagrange_equiv G X O (cs O))) hT))
      (finite_choice Or hOr (O ↦ BurnsideOrbitChoice G X O) (burnside_orbit_choice_merely G hG X hX))
