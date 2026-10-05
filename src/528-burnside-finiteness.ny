export "527-lagrange-counting"

{` Chapter 5, lem:burnside, the finiteness claims: for a finite group G and
   a finite G-set X, every X^g (FixedBy of the core), the sum
   Σ_{g : USym G} X^g and the set of orbits X/G are finite. As in the
   book's proof: X^g is a decidable subset of X(sh_G) (xca:finsets-decidable,
   rem:subset-of-fin-set), the sum is finite by xca:fin-sum-of-finsets, and
   X/G is the quotient of X(sh_G) by ∃_g (x = g · y) (cor:orbit-equiv), a
   relation decidable by xca:dec-quant-finset, hence finite by
   xca:dec-quot-finite-set. The relation is stated in the module-520 form
   ∃_g (g · x = y), which is the same equivalence relation up to symmetry. `}

{` X^g is a finite set. `}
def burnside_fixed_by_finite (G : Group) (X : GSet G) (hX : IsFiniteGSet G X) (g : USym G)
  : IsFinite (FixedBy G X g)
  ≔ let Xs ≔ gset_underlying G X in
    finite_decidable_subset Xs hX (x ↦ Id Xs (gset_usym_act G X g x) x)
      (x ↦ gset_underlying_set G X (gset_usym_act G X g x) x)
      (x ↦ finite_decidable_equality Xs hX (gset_usym_act G X g x) x)

{` The sum type Σ_{g : USym G} X^g of lem:burnside. `}
def BurnsideSum (G : Group) (X : GSet G) : Type ≔ Σ (USym G) (g ↦ FixedBy G X g)

def burnside_sum_finite (G : Group) (hG : IsFiniteGroup G) (X : GSet G) (hX : IsFiniteGSet G X)
  : IsFinite (BurnsideSum G X)
  ≔ finite_sigma (USym G) hG (g ↦ FixedBy G X g) (g ↦ burnside_fixed_by_finite G X hX g)

{` The orbit relation ∃_{g : USym G} (g · x = y) is decidable. `}
def burnside_orbit_relation_decidable (G : Group) (hG : IsFiniteGroup G) (X : GSet G) (hX : IsFiniteGSet G X)
  : DecidableRelation (gset_underlying G X) (orbit_equivalence_relation G X)
  ≔ let Xs ≔ gset_underlying G X in
    x y ↦ finite_quantifiers (USym G) hG (g ↦ Id Xs (gset_usym_act G X g x) y)
      (g ↦ gset_underlying_set G X (gset_usym_act G X g x) y)
      (g ↦ finite_decidable_equality Xs hX (gset_usym_act G X g x) y) .snd

{` X/G is a finite set. `}
def burnside_orbits_finite (G : Group) (hG : IsFiniteGroup G) (X : GSet G) (hX : IsFiniteGSet G X)
  : IsFinite (Orbits G X)
  ≔ let Xs ≔ gset_underlying G X in
    let R ≔ orbit_equivalence_relation G X in
    finite_of_equiv (Orbits G X) (Quotient Xs R)
      (canonical_inverse_equiv (Quotient Xs R) (Orbits G X)
        (native_equivalence (Quotient Xs R) (Orbits G X) (orbit_quotient_equiv G X)))
      (finite_quotient Xs hX R (burnside_orbit_relation_decidable G hG X hX))
