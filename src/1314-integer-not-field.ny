export "1310-integer-ring"
export "1301-fields"
export "125-integer-units"

{` Chapter 13 (fields.tex 1239-1276), litmus for the definitions of fields
   and local rings: ℤ is a non-trivial commutative ring that is neither a
   field nor a local ring. The units of ℤ are ±1 (integer_unit_sign,
   module 125), so 2 is non-invertible but 2 ≠ 0, and 1 = 3 + (-2) is
   invertible while neither 3 nor -2 is. `}

def integer_ring_non_trivial_cring : IsNonTrivialCRing integer_ring
  ≔ (integer_ring_commutative, integer_ring_non_trivial)

def integer_not_unit (x : Int) (h1 : Not (Id Int x int_one)) (h2 : Not (Id Int x (neg. 0)))
  : Not (IsInvertible integer_ring x)
  ≔ t ↦ mere_rec (InverseWitness integer_ring x) Empty empty_prop
      (w ↦ match integer_unit_sign x (w .fst) (w .snd .fst) [ inl. p ↦ h1 p | inr. q ↦ h2 q ]) t

def integer_two_not_invertible : Not (IsInvertible integer_ring (pos. 2))
  ≔ integer_not_unit (pos. 2) (p ↦ int_encode (pos. 2) int_one p) (p ↦ int_encode (pos. 2) (neg. 0) p)

def integer_three_not_invertible : Not (IsInvertible integer_ring (pos. 3))
  ≔ integer_not_unit (pos. 3) (p ↦ int_encode (pos. 3) int_one p) (p ↦ int_encode (pos. 3) (neg. 0) p)

def integer_minus_two_not_invertible : Not (IsInvertible integer_ring (neg. 1))
  ≔ integer_not_unit (neg. 1) (p ↦ int_encode (neg. 1) int_one p) (p ↦ int_encode (neg. 1) (neg. 0) p)

{` ℤ is not a field: a field's non-invertibles are 0, but 2 ≠ 0. `}
def integer_ring_not_field : Not (IsField integer_ring)
  ≔ h ↦ int_encode (pos. 2) int_zero (field_non_invertible_zero integer_ring h (pos. 2) integer_two_not_invertible)

def integer_three_plus_minus_two : Id Int (integer_ring .add (pos. 3) (neg. 1)) int_one ≔ refl int_one

{` ℤ is not a local ring: 3 + (-2) = 1 is invertible, 3 and -2 are not. `}
def integer_ring_not_local : Not (IsLocalRing integer_ring)
  ≔ h ↦ mere_rec (Sum (IsInvertible integer_ring (pos. 3)) (IsInvertible integer_ring (neg. 1))) Empty empty_prop
      [ inl. u ↦ integer_three_not_invertible u | inr. u ↦ integer_minus_two_not_invertible u ]
      (h .snd (pos. 3) (neg. 1) (one_invertible integer_ring))
