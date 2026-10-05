export "1302-vector-spaces"
export "450-sign-parity-basics"

{` Litmus for chapter 13: the two-element field ℤ/2 on Bool, with
   addition bool_xor (module 450) and multiplication f2_mul (conjunction,
   restated here to avoid importing the sign chain of module 456). It is a
   non-trivial commutative ring, a field in the book's sense, a discrete
   field, a local ring and a Heyting field. `}

def f2_mul (a b : Bool) : Bool ≔ match a [ false. ↦ false. | true. ↦ b ]

def f2_add_laws : AbstractGroupLaws Bool false. bool_xor (x ↦ x)
  ≔ (carrier_set ≔ bool_set,
     unit_right ≔ bool_xor_false_right,
     unit_left ≔ g ↦ refl g,
     assoc ≔ a b c ↦ inverse Bool (bool_xor (bool_xor a b) c) (bool_xor a (bool_xor b c)) (bool_xor_assoc a b c),
     inv_right ≔ bool_xor_self)

def f2_mul_one_right (a : Bool) : Id Bool (f2_mul a true.) a
  ≔ match a [ false. ↦ refl (false. : Bool) | true. ↦ refl (true. : Bool) ]

def f2_mul_assoc (a b c : Bool) : Id Bool (f2_mul a (f2_mul b c)) (f2_mul (f2_mul a b) c)
  ≔ match a [ false. ↦ refl (false. : Bool) | true. ↦ refl (f2_mul b c) ]

def f2_ldistr (a b c : Bool) : Id Bool (f2_mul a (bool_xor b c)) (bool_xor (f2_mul a b) (f2_mul a c))
  ≔ match a [ false. ↦ refl (false. : Bool) | true. ↦ refl (bool_xor b c) ]

def f2_rdistr (a b c : Bool) : Id Bool (f2_mul (bool_xor a b) c) (bool_xor (f2_mul a c) (f2_mul b c))
  ≔ match a, b, c [
  | false., false., false. ↦ refl (false. : Bool)
  | false., false., true. ↦ refl (false. : Bool)
  | false., true., false. ↦ refl (false. : Bool)
  | false., true., true. ↦ refl (true. : Bool)
  | true., false., false. ↦ refl (false. : Bool)
  | true., false., true. ↦ refl (true. : Bool)
  | true., true., false. ↦ refl (false. : Bool)
  | true., true., true. ↦ refl (false. : Bool) ]

def f2_ring : AbstractRing
  ≔ (Bool, false., bool_xor, x ↦ x, f2_add_laws, true., f2_mul,
     (bool_set, (g ↦ (f2_mul_one_right g, refl g), f2_mul_assoc)),
     (f2_ldistr, f2_rdistr))

def f2_commutative : IsCommutativeRing f2_ring
  ≔ a b ↦ match a, b [
  | false., false. ↦ refl (false. : Bool)
  | false., true. ↦ refl (false. : Bool)
  | true., false. ↦ refl (false. : Bool)
  | true., true. ↦ refl (true. : Bool) ]

def f2_non_trivial : IsNonTrivialRing f2_ring ≔ p ↦ bool_encode false. true. p

def f2_non_trivial_cring : IsNonTrivialCRing f2_ring ≔ (f2_commutative, f2_non_trivial)

def f2_non_invertibles_zero : NonInvertiblesAreZero f2_ring
  ≔ x nx ↦ match x [
  | false. ↦ refl (false. : Bool)
  | true. ↦ match nx (one_invertible f2_ring) [ ] ]

def f2_is_field : IsField f2_ring ≔ field_from_non_invertible_zero f2_ring f2_non_trivial_cring f2_non_invertibles_zero

def f2_field : Field ≔ (f2_ring, f2_is_field)

def f2_discrete : IsDiscreteField f2_ring
  ≔ (f2_is_field,
     a ↦ match a [
     | false. ↦ mere (Sum (Id Bool false. false.) (IsInvertible f2_ring false.)) (inl. (refl (false. : Bool)))
     | true. ↦ mere (Sum (Id Bool true. false.) (IsInvertible f2_ring true.)) (inr. (one_invertible f2_ring)) ])

def f2_local : IsLocalRing f2_ring
  ≔ (f2_non_trivial_cring,
     a b h ↦ match a [
     | false. ↦ mere (Sum (IsInvertible f2_ring false.) (IsInvertible f2_ring b)) (inr. h)
     | true. ↦ mere (Sum (IsInvertible f2_ring true.) (IsInvertible f2_ring b)) (inl. (one_invertible f2_ring)) ])

def f2_heyting : IsHeytingField f2_ring ≔ (f2_is_field, f2_local)

{` Litmus computations: 1 + 1 = 0 and 1 · 1 = 1 by refl. `}
def f2_one_plus_one : Id Bool (f2_ring .add (f2_ring .one) (f2_ring .one)) (f2_ring .zero) ≔ refl (false. : Bool)

def f2_one_times_one : Id Bool (f2_ring .mul (f2_ring .one) (f2_ring .one)) (f2_ring .one) ≔ refl (true. : Bool)

{` The zero ring is a ring but not non-trivial, hence not a field. `}
def zero_ring : AbstractRing
  ≔ (Unit, star., _ _ ↦ star., _ ↦ star., unit_abstract_group_laws, star., _ _ ↦ star.,
     (unit_set, (g ↦ (match g [ star. ↦ refl (star. : Unit) ], match g [ star. ↦ refl (star. : Unit) ]),
       _ _ _ ↦ refl (star. : Unit))),
     (_ _ _ ↦ refl (star. : Unit), _ _ _ ↦ refl (star. : Unit)))

def zero_ring_not_field (h : IsField zero_ring) : Empty ≔ h .fst .snd (refl (star. : Unit))
