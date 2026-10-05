export "1504-t-equivalence-criterion"
export "1506-conjugate-roots"

{` Chapter 15 litmus: the field 𝔽₄ = 𝔽₂[ω]/(ω² + ω + 1) on the type F4 with
   elements 0, 1, ω, ω² = ω + 1 (constructors f4z f4o f4w f4v), the extension
   𝔽₂ → 𝔽₄, and the Frobenius x ↦ x², a k-automorphism exchanging the two
   roots ω, ω² of X² + X + 1. Its symmetry in Gal(𝔽₄/𝔽₂) is not the unit,
   so def:galois-group is not vacuous; and as in the introduction of the
   chapter, an automorphism fixing 𝔽₂ shows that the polynomial values at
   (ω, ω²) and at (ω², ω) vanish together (galois_conjugate_roots).
   The ring laws are checked by exhaustive case analysis (generated). `}

def F4 : Type ≔ data [ f4z. | f4o. | f4w. | f4v. ]

def F4Code (x y : F4) : Type
  ≔ match x, y [
  | f4z., f4z. ↦ Unit
  | f4z., f4o. ↦ Empty
  | f4z., f4w. ↦ Empty
  | f4z., f4v. ↦ Empty
  | f4o., f4z. ↦ Empty
  | f4o., f4o. ↦ Unit
  | f4o., f4w. ↦ Empty
  | f4o., f4v. ↦ Empty
  | f4w., f4z. ↦ Empty
  | f4w., f4o. ↦ Empty
  | f4w., f4w. ↦ Unit
  | f4w., f4v. ↦ Empty
  | f4v., f4z. ↦ Empty
  | f4v., f4o. ↦ Empty
  | f4v., f4w. ↦ Empty
  | f4v., f4v. ↦ Unit
  ]

def f4_encode (x y : F4) (p : Id F4 x y) : F4Code x y
  ≔ match p [ f4z. ⤇ star. | f4o. ⤇ star. | f4w. ⤇ star. | f4v. ⤇ star. ]

def f4_decidable_equality : DecidableEquality F4
  ≔ x y ↦ match x, y [
  | f4z., f4z. ↦ inl. (refl (f4z. : F4))
  | f4z., f4o. ↦ inr. (p ↦ f4_encode f4z. f4o. p)
  | f4z., f4w. ↦ inr. (p ↦ f4_encode f4z. f4w. p)
  | f4z., f4v. ↦ inr. (p ↦ f4_encode f4z. f4v. p)
  | f4o., f4z. ↦ inr. (p ↦ f4_encode f4o. f4z. p)
  | f4o., f4o. ↦ inl. (refl (f4o. : F4))
  | f4o., f4w. ↦ inr. (p ↦ f4_encode f4o. f4w. p)
  | f4o., f4v. ↦ inr. (p ↦ f4_encode f4o. f4v. p)
  | f4w., f4z. ↦ inr. (p ↦ f4_encode f4w. f4z. p)
  | f4w., f4o. ↦ inr. (p ↦ f4_encode f4w. f4o. p)
  | f4w., f4w. ↦ inl. (refl (f4w. : F4))
  | f4w., f4v. ↦ inr. (p ↦ f4_encode f4w. f4v. p)
  | f4v., f4z. ↦ inr. (p ↦ f4_encode f4v. f4z. p)
  | f4v., f4o. ↦ inr. (p ↦ f4_encode f4v. f4o. p)
  | f4v., f4w. ↦ inr. (p ↦ f4_encode f4v. f4w. p)
  | f4v., f4v. ↦ inl. (refl (f4v. : F4))
  ]

def f4_set : isSet F4 ≔ x y ↦ hedberg F4 f4_decidable_equality x y .fst

def f4_add (x y : F4) : F4
  ≔ match x, y [
  | f4z., f4z. ↦ f4z.
  | f4z., f4o. ↦ f4o.
  | f4z., f4w. ↦ f4w.
  | f4z., f4v. ↦ f4v.
  | f4o., f4z. ↦ f4o.
  | f4o., f4o. ↦ f4z.
  | f4o., f4w. ↦ f4v.
  | f4o., f4v. ↦ f4w.
  | f4w., f4z. ↦ f4w.
  | f4w., f4o. ↦ f4v.
  | f4w., f4w. ↦ f4z.
  | f4w., f4v. ↦ f4o.
  | f4v., f4z. ↦ f4v.
  | f4v., f4o. ↦ f4w.
  | f4v., f4w. ↦ f4o.
  | f4v., f4v. ↦ f4z.
  ]

def f4_mul (x y : F4) : F4
  ≔ match x, y [
  | f4z., f4z. ↦ f4z.
  | f4z., f4o. ↦ f4z.
  | f4z., f4w. ↦ f4z.
  | f4z., f4v. ↦ f4z.
  | f4o., f4z. ↦ f4z.
  | f4o., f4o. ↦ f4o.
  | f4o., f4w. ↦ f4w.
  | f4o., f4v. ↦ f4v.
  | f4w., f4z. ↦ f4z.
  | f4w., f4o. ↦ f4w.
  | f4w., f4w. ↦ f4v.
  | f4w., f4v. ↦ f4o.
  | f4v., f4z. ↦ f4z.
  | f4v., f4o. ↦ f4v.
  | f4v., f4w. ↦ f4o.
  | f4v., f4v. ↦ f4w.
  ]

def f4_add_unit_right (a : F4) : Id F4 (f4_add a f4z.) a
  ≔ match a [
  | f4z. ↦ refl (f4z. : F4)
  | f4o. ↦ refl (f4o. : F4)
  | f4w. ↦ refl (f4w. : F4)
  | f4v. ↦ refl (f4v. : F4)
  ]

def f4_add_unit_left (a : F4) : Id F4 (f4_add f4z. a) a
  ≔ match a [
  | f4z. ↦ refl (f4z. : F4)
  | f4o. ↦ refl (f4o. : F4)
  | f4w. ↦ refl (f4w. : F4)
  | f4v. ↦ refl (f4v. : F4)
  ]

def f4_add_self (a : F4) : Id F4 (f4_add a a) f4z.
  ≔ match a [
  | f4z. ↦ refl (f4z. : F4)
  | f4o. ↦ refl (f4z. : F4)
  | f4w. ↦ refl (f4z. : F4)
  | f4v. ↦ refl (f4z. : F4)
  ]

def f4_add_assoc (a b d : F4) : Id F4 (f4_add a (f4_add b d)) (f4_add (f4_add a b) d)
  ≔ match a, b, d [
  | f4z., f4z., f4z. ↦ refl (f4z. : F4)
  | f4z., f4z., f4o. ↦ refl (f4o. : F4)
  | f4z., f4z., f4w. ↦ refl (f4w. : F4)
  | f4z., f4z., f4v. ↦ refl (f4v. : F4)
  | f4z., f4o., f4z. ↦ refl (f4o. : F4)
  | f4z., f4o., f4o. ↦ refl (f4z. : F4)
  | f4z., f4o., f4w. ↦ refl (f4v. : F4)
  | f4z., f4o., f4v. ↦ refl (f4w. : F4)
  | f4z., f4w., f4z. ↦ refl (f4w. : F4)
  | f4z., f4w., f4o. ↦ refl (f4v. : F4)
  | f4z., f4w., f4w. ↦ refl (f4z. : F4)
  | f4z., f4w., f4v. ↦ refl (f4o. : F4)
  | f4z., f4v., f4z. ↦ refl (f4v. : F4)
  | f4z., f4v., f4o. ↦ refl (f4w. : F4)
  | f4z., f4v., f4w. ↦ refl (f4o. : F4)
  | f4z., f4v., f4v. ↦ refl (f4z. : F4)
  | f4o., f4z., f4z. ↦ refl (f4o. : F4)
  | f4o., f4z., f4o. ↦ refl (f4z. : F4)
  | f4o., f4z., f4w. ↦ refl (f4v. : F4)
  | f4o., f4z., f4v. ↦ refl (f4w. : F4)
  | f4o., f4o., f4z. ↦ refl (f4z. : F4)
  | f4o., f4o., f4o. ↦ refl (f4o. : F4)
  | f4o., f4o., f4w. ↦ refl (f4w. : F4)
  | f4o., f4o., f4v. ↦ refl (f4v. : F4)
  | f4o., f4w., f4z. ↦ refl (f4v. : F4)
  | f4o., f4w., f4o. ↦ refl (f4w. : F4)
  | f4o., f4w., f4w. ↦ refl (f4o. : F4)
  | f4o., f4w., f4v. ↦ refl (f4z. : F4)
  | f4o., f4v., f4z. ↦ refl (f4w. : F4)
  | f4o., f4v., f4o. ↦ refl (f4v. : F4)
  | f4o., f4v., f4w. ↦ refl (f4z. : F4)
  | f4o., f4v., f4v. ↦ refl (f4o. : F4)
  | f4w., f4z., f4z. ↦ refl (f4w. : F4)
  | f4w., f4z., f4o. ↦ refl (f4v. : F4)
  | f4w., f4z., f4w. ↦ refl (f4z. : F4)
  | f4w., f4z., f4v. ↦ refl (f4o. : F4)
  | f4w., f4o., f4z. ↦ refl (f4v. : F4)
  | f4w., f4o., f4o. ↦ refl (f4w. : F4)
  | f4w., f4o., f4w. ↦ refl (f4o. : F4)
  | f4w., f4o., f4v. ↦ refl (f4z. : F4)
  | f4w., f4w., f4z. ↦ refl (f4z. : F4)
  | f4w., f4w., f4o. ↦ refl (f4o. : F4)
  | f4w., f4w., f4w. ↦ refl (f4w. : F4)
  | f4w., f4w., f4v. ↦ refl (f4v. : F4)
  | f4w., f4v., f4z. ↦ refl (f4o. : F4)
  | f4w., f4v., f4o. ↦ refl (f4z. : F4)
  | f4w., f4v., f4w. ↦ refl (f4v. : F4)
  | f4w., f4v., f4v. ↦ refl (f4w. : F4)
  | f4v., f4z., f4z. ↦ refl (f4v. : F4)
  | f4v., f4z., f4o. ↦ refl (f4w. : F4)
  | f4v., f4z., f4w. ↦ refl (f4o. : F4)
  | f4v., f4z., f4v. ↦ refl (f4z. : F4)
  | f4v., f4o., f4z. ↦ refl (f4w. : F4)
  | f4v., f4o., f4o. ↦ refl (f4v. : F4)
  | f4v., f4o., f4w. ↦ refl (f4z. : F4)
  | f4v., f4o., f4v. ↦ refl (f4o. : F4)
  | f4v., f4w., f4z. ↦ refl (f4o. : F4)
  | f4v., f4w., f4o. ↦ refl (f4z. : F4)
  | f4v., f4w., f4w. ↦ refl (f4v. : F4)
  | f4v., f4w., f4v. ↦ refl (f4w. : F4)
  | f4v., f4v., f4z. ↦ refl (f4z. : F4)
  | f4v., f4v., f4o. ↦ refl (f4o. : F4)
  | f4v., f4v., f4w. ↦ refl (f4w. : F4)
  | f4v., f4v., f4v. ↦ refl (f4v. : F4)
  ]

def f4_mul_one_right (a : F4) : Id F4 (f4_mul a f4o.) a
  ≔ match a [
  | f4z. ↦ refl (f4z. : F4)
  | f4o. ↦ refl (f4o. : F4)
  | f4w. ↦ refl (f4w. : F4)
  | f4v. ↦ refl (f4v. : F4)
  ]

def f4_mul_one_left (a : F4) : Id F4 (f4_mul f4o. a) a
  ≔ match a [
  | f4z. ↦ refl (f4z. : F4)
  | f4o. ↦ refl (f4o. : F4)
  | f4w. ↦ refl (f4w. : F4)
  | f4v. ↦ refl (f4v. : F4)
  ]

def f4_mul_assoc (a b d : F4) : Id F4 (f4_mul a (f4_mul b d)) (f4_mul (f4_mul a b) d)
  ≔ match a, b, d [
  | f4z., f4z., f4z. ↦ refl (f4z. : F4)
  | f4z., f4z., f4o. ↦ refl (f4z. : F4)
  | f4z., f4z., f4w. ↦ refl (f4z. : F4)
  | f4z., f4z., f4v. ↦ refl (f4z. : F4)
  | f4z., f4o., f4z. ↦ refl (f4z. : F4)
  | f4z., f4o., f4o. ↦ refl (f4z. : F4)
  | f4z., f4o., f4w. ↦ refl (f4z. : F4)
  | f4z., f4o., f4v. ↦ refl (f4z. : F4)
  | f4z., f4w., f4z. ↦ refl (f4z. : F4)
  | f4z., f4w., f4o. ↦ refl (f4z. : F4)
  | f4z., f4w., f4w. ↦ refl (f4z. : F4)
  | f4z., f4w., f4v. ↦ refl (f4z. : F4)
  | f4z., f4v., f4z. ↦ refl (f4z. : F4)
  | f4z., f4v., f4o. ↦ refl (f4z. : F4)
  | f4z., f4v., f4w. ↦ refl (f4z. : F4)
  | f4z., f4v., f4v. ↦ refl (f4z. : F4)
  | f4o., f4z., f4z. ↦ refl (f4z. : F4)
  | f4o., f4z., f4o. ↦ refl (f4z. : F4)
  | f4o., f4z., f4w. ↦ refl (f4z. : F4)
  | f4o., f4z., f4v. ↦ refl (f4z. : F4)
  | f4o., f4o., f4z. ↦ refl (f4z. : F4)
  | f4o., f4o., f4o. ↦ refl (f4o. : F4)
  | f4o., f4o., f4w. ↦ refl (f4w. : F4)
  | f4o., f4o., f4v. ↦ refl (f4v. : F4)
  | f4o., f4w., f4z. ↦ refl (f4z. : F4)
  | f4o., f4w., f4o. ↦ refl (f4w. : F4)
  | f4o., f4w., f4w. ↦ refl (f4v. : F4)
  | f4o., f4w., f4v. ↦ refl (f4o. : F4)
  | f4o., f4v., f4z. ↦ refl (f4z. : F4)
  | f4o., f4v., f4o. ↦ refl (f4v. : F4)
  | f4o., f4v., f4w. ↦ refl (f4o. : F4)
  | f4o., f4v., f4v. ↦ refl (f4w. : F4)
  | f4w., f4z., f4z. ↦ refl (f4z. : F4)
  | f4w., f4z., f4o. ↦ refl (f4z. : F4)
  | f4w., f4z., f4w. ↦ refl (f4z. : F4)
  | f4w., f4z., f4v. ↦ refl (f4z. : F4)
  | f4w., f4o., f4z. ↦ refl (f4z. : F4)
  | f4w., f4o., f4o. ↦ refl (f4w. : F4)
  | f4w., f4o., f4w. ↦ refl (f4v. : F4)
  | f4w., f4o., f4v. ↦ refl (f4o. : F4)
  | f4w., f4w., f4z. ↦ refl (f4z. : F4)
  | f4w., f4w., f4o. ↦ refl (f4v. : F4)
  | f4w., f4w., f4w. ↦ refl (f4o. : F4)
  | f4w., f4w., f4v. ↦ refl (f4w. : F4)
  | f4w., f4v., f4z. ↦ refl (f4z. : F4)
  | f4w., f4v., f4o. ↦ refl (f4o. : F4)
  | f4w., f4v., f4w. ↦ refl (f4w. : F4)
  | f4w., f4v., f4v. ↦ refl (f4v. : F4)
  | f4v., f4z., f4z. ↦ refl (f4z. : F4)
  | f4v., f4z., f4o. ↦ refl (f4z. : F4)
  | f4v., f4z., f4w. ↦ refl (f4z. : F4)
  | f4v., f4z., f4v. ↦ refl (f4z. : F4)
  | f4v., f4o., f4z. ↦ refl (f4z. : F4)
  | f4v., f4o., f4o. ↦ refl (f4v. : F4)
  | f4v., f4o., f4w. ↦ refl (f4o. : F4)
  | f4v., f4o., f4v. ↦ refl (f4w. : F4)
  | f4v., f4w., f4z. ↦ refl (f4z. : F4)
  | f4v., f4w., f4o. ↦ refl (f4o. : F4)
  | f4v., f4w., f4w. ↦ refl (f4w. : F4)
  | f4v., f4w., f4v. ↦ refl (f4v. : F4)
  | f4v., f4v., f4z. ↦ refl (f4z. : F4)
  | f4v., f4v., f4o. ↦ refl (f4w. : F4)
  | f4v., f4v., f4w. ↦ refl (f4v. : F4)
  | f4v., f4v., f4v. ↦ refl (f4o. : F4)
  ]

def f4_ldistr (a b d : F4) : Id F4 (f4_mul a (f4_add b d)) (f4_add (f4_mul a b) (f4_mul a d))
  ≔ match a, b, d [
  | f4z., f4z., f4z. ↦ refl (f4z. : F4)
  | f4z., f4z., f4o. ↦ refl (f4z. : F4)
  | f4z., f4z., f4w. ↦ refl (f4z. : F4)
  | f4z., f4z., f4v. ↦ refl (f4z. : F4)
  | f4z., f4o., f4z. ↦ refl (f4z. : F4)
  | f4z., f4o., f4o. ↦ refl (f4z. : F4)
  | f4z., f4o., f4w. ↦ refl (f4z. : F4)
  | f4z., f4o., f4v. ↦ refl (f4z. : F4)
  | f4z., f4w., f4z. ↦ refl (f4z. : F4)
  | f4z., f4w., f4o. ↦ refl (f4z. : F4)
  | f4z., f4w., f4w. ↦ refl (f4z. : F4)
  | f4z., f4w., f4v. ↦ refl (f4z. : F4)
  | f4z., f4v., f4z. ↦ refl (f4z. : F4)
  | f4z., f4v., f4o. ↦ refl (f4z. : F4)
  | f4z., f4v., f4w. ↦ refl (f4z. : F4)
  | f4z., f4v., f4v. ↦ refl (f4z. : F4)
  | f4o., f4z., f4z. ↦ refl (f4z. : F4)
  | f4o., f4z., f4o. ↦ refl (f4o. : F4)
  | f4o., f4z., f4w. ↦ refl (f4w. : F4)
  | f4o., f4z., f4v. ↦ refl (f4v. : F4)
  | f4o., f4o., f4z. ↦ refl (f4o. : F4)
  | f4o., f4o., f4o. ↦ refl (f4z. : F4)
  | f4o., f4o., f4w. ↦ refl (f4v. : F4)
  | f4o., f4o., f4v. ↦ refl (f4w. : F4)
  | f4o., f4w., f4z. ↦ refl (f4w. : F4)
  | f4o., f4w., f4o. ↦ refl (f4v. : F4)
  | f4o., f4w., f4w. ↦ refl (f4z. : F4)
  | f4o., f4w., f4v. ↦ refl (f4o. : F4)
  | f4o., f4v., f4z. ↦ refl (f4v. : F4)
  | f4o., f4v., f4o. ↦ refl (f4w. : F4)
  | f4o., f4v., f4w. ↦ refl (f4o. : F4)
  | f4o., f4v., f4v. ↦ refl (f4z. : F4)
  | f4w., f4z., f4z. ↦ refl (f4z. : F4)
  | f4w., f4z., f4o. ↦ refl (f4w. : F4)
  | f4w., f4z., f4w. ↦ refl (f4v. : F4)
  | f4w., f4z., f4v. ↦ refl (f4o. : F4)
  | f4w., f4o., f4z. ↦ refl (f4w. : F4)
  | f4w., f4o., f4o. ↦ refl (f4z. : F4)
  | f4w., f4o., f4w. ↦ refl (f4o. : F4)
  | f4w., f4o., f4v. ↦ refl (f4v. : F4)
  | f4w., f4w., f4z. ↦ refl (f4v. : F4)
  | f4w., f4w., f4o. ↦ refl (f4o. : F4)
  | f4w., f4w., f4w. ↦ refl (f4z. : F4)
  | f4w., f4w., f4v. ↦ refl (f4w. : F4)
  | f4w., f4v., f4z. ↦ refl (f4o. : F4)
  | f4w., f4v., f4o. ↦ refl (f4v. : F4)
  | f4w., f4v., f4w. ↦ refl (f4w. : F4)
  | f4w., f4v., f4v. ↦ refl (f4z. : F4)
  | f4v., f4z., f4z. ↦ refl (f4z. : F4)
  | f4v., f4z., f4o. ↦ refl (f4v. : F4)
  | f4v., f4z., f4w. ↦ refl (f4o. : F4)
  | f4v., f4z., f4v. ↦ refl (f4w. : F4)
  | f4v., f4o., f4z. ↦ refl (f4v. : F4)
  | f4v., f4o., f4o. ↦ refl (f4z. : F4)
  | f4v., f4o., f4w. ↦ refl (f4w. : F4)
  | f4v., f4o., f4v. ↦ refl (f4o. : F4)
  | f4v., f4w., f4z. ↦ refl (f4o. : F4)
  | f4v., f4w., f4o. ↦ refl (f4w. : F4)
  | f4v., f4w., f4w. ↦ refl (f4z. : F4)
  | f4v., f4w., f4v. ↦ refl (f4v. : F4)
  | f4v., f4v., f4z. ↦ refl (f4w. : F4)
  | f4v., f4v., f4o. ↦ refl (f4o. : F4)
  | f4v., f4v., f4w. ↦ refl (f4v. : F4)
  | f4v., f4v., f4v. ↦ refl (f4z. : F4)
  ]

def f4_rdistr (a b d : F4) : Id F4 (f4_mul (f4_add a b) d) (f4_add (f4_mul a d) (f4_mul b d))
  ≔ match a, b, d [
  | f4z., f4z., f4z. ↦ refl (f4z. : F4)
  | f4z., f4z., f4o. ↦ refl (f4z. : F4)
  | f4z., f4z., f4w. ↦ refl (f4z. : F4)
  | f4z., f4z., f4v. ↦ refl (f4z. : F4)
  | f4z., f4o., f4z. ↦ refl (f4z. : F4)
  | f4z., f4o., f4o. ↦ refl (f4o. : F4)
  | f4z., f4o., f4w. ↦ refl (f4w. : F4)
  | f4z., f4o., f4v. ↦ refl (f4v. : F4)
  | f4z., f4w., f4z. ↦ refl (f4z. : F4)
  | f4z., f4w., f4o. ↦ refl (f4w. : F4)
  | f4z., f4w., f4w. ↦ refl (f4v. : F4)
  | f4z., f4w., f4v. ↦ refl (f4o. : F4)
  | f4z., f4v., f4z. ↦ refl (f4z. : F4)
  | f4z., f4v., f4o. ↦ refl (f4v. : F4)
  | f4z., f4v., f4w. ↦ refl (f4o. : F4)
  | f4z., f4v., f4v. ↦ refl (f4w. : F4)
  | f4o., f4z., f4z. ↦ refl (f4z. : F4)
  | f4o., f4z., f4o. ↦ refl (f4o. : F4)
  | f4o., f4z., f4w. ↦ refl (f4w. : F4)
  | f4o., f4z., f4v. ↦ refl (f4v. : F4)
  | f4o., f4o., f4z. ↦ refl (f4z. : F4)
  | f4o., f4o., f4o. ↦ refl (f4z. : F4)
  | f4o., f4o., f4w. ↦ refl (f4z. : F4)
  | f4o., f4o., f4v. ↦ refl (f4z. : F4)
  | f4o., f4w., f4z. ↦ refl (f4z. : F4)
  | f4o., f4w., f4o. ↦ refl (f4v. : F4)
  | f4o., f4w., f4w. ↦ refl (f4o. : F4)
  | f4o., f4w., f4v. ↦ refl (f4w. : F4)
  | f4o., f4v., f4z. ↦ refl (f4z. : F4)
  | f4o., f4v., f4o. ↦ refl (f4w. : F4)
  | f4o., f4v., f4w. ↦ refl (f4v. : F4)
  | f4o., f4v., f4v. ↦ refl (f4o. : F4)
  | f4w., f4z., f4z. ↦ refl (f4z. : F4)
  | f4w., f4z., f4o. ↦ refl (f4w. : F4)
  | f4w., f4z., f4w. ↦ refl (f4v. : F4)
  | f4w., f4z., f4v. ↦ refl (f4o. : F4)
  | f4w., f4o., f4z. ↦ refl (f4z. : F4)
  | f4w., f4o., f4o. ↦ refl (f4v. : F4)
  | f4w., f4o., f4w. ↦ refl (f4o. : F4)
  | f4w., f4o., f4v. ↦ refl (f4w. : F4)
  | f4w., f4w., f4z. ↦ refl (f4z. : F4)
  | f4w., f4w., f4o. ↦ refl (f4z. : F4)
  | f4w., f4w., f4w. ↦ refl (f4z. : F4)
  | f4w., f4w., f4v. ↦ refl (f4z. : F4)
  | f4w., f4v., f4z. ↦ refl (f4z. : F4)
  | f4w., f4v., f4o. ↦ refl (f4o. : F4)
  | f4w., f4v., f4w. ↦ refl (f4w. : F4)
  | f4w., f4v., f4v. ↦ refl (f4v. : F4)
  | f4v., f4z., f4z. ↦ refl (f4z. : F4)
  | f4v., f4z., f4o. ↦ refl (f4v. : F4)
  | f4v., f4z., f4w. ↦ refl (f4o. : F4)
  | f4v., f4z., f4v. ↦ refl (f4w. : F4)
  | f4v., f4o., f4z. ↦ refl (f4z. : F4)
  | f4v., f4o., f4o. ↦ refl (f4w. : F4)
  | f4v., f4o., f4w. ↦ refl (f4v. : F4)
  | f4v., f4o., f4v. ↦ refl (f4o. : F4)
  | f4v., f4w., f4z. ↦ refl (f4z. : F4)
  | f4v., f4w., f4o. ↦ refl (f4o. : F4)
  | f4v., f4w., f4w. ↦ refl (f4w. : F4)
  | f4v., f4w., f4v. ↦ refl (f4v. : F4)
  | f4v., f4v., f4z. ↦ refl (f4z. : F4)
  | f4v., f4v., f4o. ↦ refl (f4z. : F4)
  | f4v., f4v., f4w. ↦ refl (f4z. : F4)
  | f4v., f4v., f4v. ↦ refl (f4z. : F4)
  ]

def f4_mul_comm (a b : F4) : Id F4 (f4_mul a b) (f4_mul b a)
  ≔ match a, b [
  | f4z., f4z. ↦ refl (f4z. : F4)
  | f4z., f4o. ↦ refl (f4z. : F4)
  | f4z., f4w. ↦ refl (f4z. : F4)
  | f4z., f4v. ↦ refl (f4z. : F4)
  | f4o., f4z. ↦ refl (f4z. : F4)
  | f4o., f4o. ↦ refl (f4o. : F4)
  | f4o., f4w. ↦ refl (f4w. : F4)
  | f4o., f4v. ↦ refl (f4v. : F4)
  | f4w., f4z. ↦ refl (f4z. : F4)
  | f4w., f4o. ↦ refl (f4w. : F4)
  | f4w., f4w. ↦ refl (f4v. : F4)
  | f4w., f4v. ↦ refl (f4o. : F4)
  | f4v., f4z. ↦ refl (f4z. : F4)
  | f4v., f4o. ↦ refl (f4v. : F4)
  | f4v., f4w. ↦ refl (f4o. : F4)
  | f4v., f4v. ↦ refl (f4w. : F4)
  ]

def f4_ring : AbstractRing
  ≔ (F4, f4z., f4_add, x ↦ x,
     (carrier_set ≔ f4_set, unit_right ≔ f4_add_unit_right, unit_left ≔ f4_add_unit_left,
      assoc ≔ f4_add_assoc, inv_right ≔ f4_add_self),
     f4o., f4_mul,
     (f4_set, (g ↦ (f4_mul_one_right g, f4_mul_one_left g), f4_mul_assoc)),
     (f4_ldistr, f4_rdistr))

def f4_non_trivial : IsNonTrivialRing f4_ring ≔ p ↦ f4_encode f4z. f4o. p

def f4_non_trivial_cring : IsNonTrivialCRing f4_ring ≔ (f4_mul_comm, f4_non_trivial)

def f4_non_invertibles_zero : NonInvertiblesAreZero f4_ring
  ≔ x nx ↦ match x [
  | f4z. ↦ refl (f4z. : F4)
  | f4o. ↦ match nx (invertible_intro f4_ring f4o. f4o. (refl (f4o. : F4)) (refl (f4o. : F4))) [ ]
  | f4w. ↦ match nx (invertible_intro f4_ring f4w. f4v. (refl (f4o. : F4)) (refl (f4o. : F4))) [ ]
  | f4v. ↦ match nx (invertible_intro f4_ring f4v. f4w. (refl (f4o. : F4)) (refl (f4o. : F4))) [ ] ]

def f4_field : Field ≔ (f4_ring, field_from_non_invertible_zero f4_ring f4_non_trivial_cring f4_non_invertibles_zero)

{` Litmus: ω² = ω + 1 and ω³ = 1. `}
def f4_omega_square : Id F4 (f4_mul f4w. f4w.) (f4_add f4w. f4o.) ≔ refl (f4v. : F4)

def f4_omega_cube : Id F4 (f4_mul f4w. (f4_mul f4w. f4w.)) f4o. ≔ refl (f4o. : F4)

{` The extension 𝔽₂ → 𝔽₄. `}
def f2_to_f4 (b : Bool) : F4 ≔ match b [ false. ↦ f4z. | true. ↦ f4o. ]

def f2_to_f4_hom : RingHom f2_ring f4_ring
  ≔ ((f2_to_f4, a b ↦ match a, b [
  | false., false. ↦ refl (f4z. : F4)
  | false., true. ↦ refl (f4o. : F4)
  | true., false. ↦ refl (f4o. : F4)
  | true., true. ↦ refl (f4z. : F4)
  ]),
     (refl (f4o. : F4), a b ↦ match a, b [
  | false., false. ↦ refl (f4z. : F4)
  | false., true. ↦ refl (f4z. : F4)
  | true., false. ↦ refl (f4z. : F4)
  | true., true. ↦ refl (f4o. : F4)
  ]))

def f4_over_f2 : FieldExt f2_field ≔ (f4_field, f2_to_f4_hom)

def f4_frobenius (a : F4) : F4
  ≔ match a [
  | f4z. ↦ (f4z.)
  | f4o. ↦ (f4o.)
  | f4w. ↦ (f4v.)
  | f4v. ↦ (f4w.)
  ]
def f4_frobenius_involutive (a : F4) : Id F4 (f4_frobenius (f4_frobenius a)) a
  ≔ match a [
  | f4z. ↦ refl (f4z. : F4)
  | f4o. ↦ refl (f4o. : F4)
  | f4w. ↦ refl (f4w. : F4)
  | f4v. ↦ refl (f4v. : F4)
  ]

def f4_frobenius_add (a b : F4) : Id F4 (f4_frobenius (f4_add a b)) (f4_add (f4_frobenius a) (f4_frobenius b))
  ≔ match a, b [
  | f4z., f4z. ↦ refl (f4z. : F4)
  | f4z., f4o. ↦ refl (f4o. : F4)
  | f4z., f4w. ↦ refl (f4v. : F4)
  | f4z., f4v. ↦ refl (f4w. : F4)
  | f4o., f4z. ↦ refl (f4o. : F4)
  | f4o., f4o. ↦ refl (f4z. : F4)
  | f4o., f4w. ↦ refl (f4w. : F4)
  | f4o., f4v. ↦ refl (f4v. : F4)
  | f4w., f4z. ↦ refl (f4v. : F4)
  | f4w., f4o. ↦ refl (f4w. : F4)
  | f4w., f4w. ↦ refl (f4z. : F4)
  | f4w., f4v. ↦ refl (f4o. : F4)
  | f4v., f4z. ↦ refl (f4w. : F4)
  | f4v., f4o. ↦ refl (f4v. : F4)
  | f4v., f4w. ↦ refl (f4o. : F4)
  | f4v., f4v. ↦ refl (f4z. : F4)
  ]

def f4_frobenius_mul (a b : F4) : Id F4 (f4_frobenius (f4_mul a b)) (f4_mul (f4_frobenius a) (f4_frobenius b))
  ≔ match a, b [
  | f4z., f4z. ↦ refl (f4z. : F4)
  | f4z., f4o. ↦ refl (f4z. : F4)
  | f4z., f4w. ↦ refl (f4z. : F4)
  | f4z., f4v. ↦ refl (f4z. : F4)
  | f4o., f4z. ↦ refl (f4z. : F4)
  | f4o., f4o. ↦ refl (f4o. : F4)
  | f4o., f4w. ↦ refl (f4v. : F4)
  | f4o., f4v. ↦ refl (f4w. : F4)
  | f4w., f4z. ↦ refl (f4z. : F4)
  | f4w., f4o. ↦ refl (f4v. : F4)
  | f4w., f4w. ↦ refl (f4w. : F4)
  | f4w., f4v. ↦ refl (f4o. : F4)
  | f4v., f4z. ↦ refl (f4z. : F4)
  | f4v., f4o. ↦ refl (f4w. : F4)
  | f4v., f4w. ↦ refl (f4o. : F4)
  | f4v., f4v. ↦ refl (f4v. : F4)
  ]

def f4_frobenius_iso : FieldIso f4_field f4_field
  ≔ (quasi_inverse_equiv F4 F4 f4_frobenius f4_frobenius f4_frobenius_involutive f4_frobenius_involutive,
     (f4_frobenius_add, (f4_frobenius_mul, (refl (f4z. : F4), refl (f4o. : F4)))))

{` The Frobenius as a k-automorphism of 𝔽₄ over 𝔽₂ (it fixes 0 and 1). `}
def f4_frobenius_kaut : FieldExtIso f2_field f4_over_f2 f4_over_f2
  ≔ (f4_frobenius_iso,
     ring_hom_ext f2_ring f4_ring (field_iso_after f2_field f4_field f4_field f2_to_f4_hom f4_frobenius_iso) f2_to_f4_hom
       (b ↦ match b [ false. ↦ refl (f4z. : F4) | true. ↦ refl (f4o. : F4) ]))

def f4_frobenius_symmetry : USym (galois_group f2_field f4_over_f2)
  ≔ equiv_inverse_map (USym (galois_group f2_field f4_over_f2)) (FieldExtIso f2_field f4_over_f2 f4_over_f2)
      (galois_usym_kaut_equiv f2_field f4_over_f2) f4_frobenius_kaut

def f4_kaut_eval (σ : FieldExtIso f2_field f4_over_f2 f4_over_f2) : F4 ≔ σ .fst .fst .map f4w.

{` Litmus for def:galois-group: the Frobenius symmetry is not the unit of Gal(𝔽₄/𝔽₂). `}
def f4_frobenius_symmetry_nontrivial
  (p : Id (USym (galois_group f2_field f4_over_f2)) f4_frobenius_symmetry (usym_unit (galois_group f2_field f4_over_f2)))
  : Empty
  ≔ let U ≔ USym (galois_group f2_field f4_over_f2) in
    let I ≔ FieldExtIso f2_field f4_over_f2 f4_over_f2 in
    let e ≔ galois_usym_kaut_equiv f2_field f4_over_f2 in
    f4_encode f4v. f4w.
      (concat F4 f4v. (f4_kaut_eval (e .map f4_frobenius_symmetry)) f4w.
        (refl f4_kaut_eval (inverse I (e .map f4_frobenius_symmetry) f4_frobenius_kaut (equiv_counit U I e f4_frobenius_kaut)))
        (concat F4 (f4_kaut_eval (e .map f4_frobenius_symmetry)) (f4_kaut_eval (e .map (usym_unit (galois_group f2_field f4_over_f2)))) f4w.
          (refl ((g ↦ f4_kaut_eval (e .map g)) : U → F4) p)
          (inverse F4 f4w. (refl F4 .trr f4w.) (refl F4 .liftr f4w.))))

{` The introduction's claim for 𝔽₂ → 𝔽₄: ω and ω² are roots of X² + X + 1,
   and Q(ω, ω²) = 0 iff Q(ω², ω) = 0 for every polynomial Q over 𝔽₂. `}
def f4_omega_root : Id F4 (poly_value f4_ring f4w. (suc. (suc. zero.)) (_ ↦ f4o.)) f4z. ≔ refl (f4z. : F4)

def f4_omega_square_root : Id F4 (poly_value f4_ring f4v. (suc. (suc. zero.)) (_ ↦ f4o.)) f4z. ≔ refl (f4z. : F4)

def f4_conjugate_roots (n m : Nat) (a : Fin (suc. n) → Fin (suc. m) → Bool)
  : Product
      (Id F4 (poly2_value f2_field f4_over_f2 n m a f4w. f4v.) f4z. → Id F4 (poly2_value f2_field f4_over_f2 n m a f4v. f4w.) f4z.)
      (Id F4 (poly2_value f2_field f4_over_f2 n m a f4v. f4w.) f4z. → Id F4 (poly2_value f2_field f4_over_f2 n m a f4w. f4v.) f4z.)
  ≔ conjugate_roots_iff f2_field f4_over_f2 f4_frobenius_kaut f4w. f4v. (refl (f4v. : F4)) (refl (f4w. : F4)) n m a
