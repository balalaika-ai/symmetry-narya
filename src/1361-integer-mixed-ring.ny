export "1360-mixed-rings"
export "435-circle-group-homomorphisms"
export "418-cyclic-group-images"
export "486-universe-not-groupoid"

{` Chapter 13, the example after def:mixring (fields.tex 143-155): the
   integers as a mixed ring, for an arbitrary circle C (ℤ = circle_group C).
   1_ℤ ≔ loop; ℓ_g is the homomorphism classified by the pointed map
   base ↦ base, loop ↦ g (circle_group_hom_from_symmetry of module 435;
   the book's "pointed by reflexivity" becomes the inverse of the base
   computation identification of the circle signature, which is refl
   whenever that computation is); r ≔ ℓ. We verify the unit laws, the
   coherence law, the associativity law, commutativity (ℓ = r by refl) and
   non-triviality (loop ≠ refl).

   Method: (ℓ_g)(h) = g^{w(h)} for the winding number w, so
   w(g · h) = w(g) w(h) and coherence follows from commutativity of
   integer multiplication; homomorphisms ℤ → ℤ are determined by their
   value at loop (ev of module 435). `}

def integer_mixed_left (C : CircleSignature) (g : USym (circle_group C)) : GroupHom (circle_group C) (circle_group C)
  ≔ circle_group_hom_from_symmetry C (circle_group C) g

{` Homomorphisms out of ℤ agree when they agree at loop. `}
def circle_hom_from_loop_agreement (C : CircleSignature) (G : Group) (f f' : GroupHom (circle_group C) G)
  (e : Id (USym G) (usym_hom (circle_group C) G f (circle_group_loop C)) (usym_hom (circle_group C) G f' (circle_group_loop C)))
  : Id (GroupHom (circle_group C) G) f f'
  ≔ equivalence_injective (GroupHom (circle_group C) G) (USym G) (circle_group_hom_ev C G) f f' e

{` Symmetries of ℤ agree when their winding numbers agree. `}
def circle_symmetry_from_winding (C : CircleSignature) (x y : USym (circle_group C))
  (e : Id Int (circle_winding C x) (circle_winding C y)) : Id (USym (circle_group C)) x y
  ≔ let U ≔ USym (circle_group C) in
    calc
      x = circle_power C (circle_winding C x)
        by inverse U (circle_power C (circle_winding C x)) x (circle_power_winding C x)
      = circle_power C (circle_winding C y) by refl (circle_power C) e
      = y by circle_power_winding C y ∎

{` (ℓ_g)(h) = g^{w(h)}. `}
def integer_mixed_value (C : CircleSignature) (g h : USym (circle_group C))
  : Id (USym (circle_group C)) (usym_hom (circle_group C) (circle_group C) (integer_mixed_left C g) h)
      (loop_power (C .carrier) (C .base) g (circle_winding C h))
  ≔ let Z ≔ circle_group C in let U ≔ USym Z in let f ≔ integer_mixed_left C g in
    calc
      usym_hom Z Z f h = usym_hom Z Z f (circle_power C (circle_winding C h))
        by refl (usym_hom Z Z f) (inverse U (circle_power C (circle_winding C h)) h (circle_power_winding C h))
      = loop_power (C .carrier) (C .base) (usym_hom Z Z f (C .loop)) (circle_winding C h)
        by loops_map_power (BG Z) (BG Z) (hom_B Z Z f) (C .loop) (circle_winding C h)
      = loop_power (C .carrier) (C .base) g (circle_winding C h)
        by refl ((x ↦ loop_power (C .carrier) (C .base) x (circle_winding C h)) : U → U)
          (circle_group_hom_from_symmetry_loop C Z g) ∎

{` w(g · h) = w(g) · w(h). `}
def integer_mixed_winding (C : CircleSignature) (g h : USym (circle_group C))
  : Id Int (circle_winding C (usym_hom (circle_group C) (circle_group C) (integer_mixed_left C g) h))
      (int_mul (circle_winding C g) (circle_winding C h))
  ≔ concat Int (circle_winding C (usym_hom (circle_group C) (circle_group C) (integer_mixed_left C g) h))
      (circle_winding C (loop_power (C .carrier) (C .base) g (circle_winding C h)))
      (int_mul (circle_winding C g) (circle_winding C h))
      (refl (circle_winding C) (integer_mixed_value C g h))
      (circle_winding_power_arbitrary C g (circle_winding C h))

def integer_mixed_coherence (C : CircleSignature) (g h : USym (circle_group C))
  : Id (USym (circle_group C)) (usym_hom (circle_group C) (circle_group C) (integer_mixed_left C g) h)
      (usym_hom (circle_group C) (circle_group C) (integer_mixed_left C h) g)
  ≔ let Z ≔ circle_group C in
    circle_symmetry_from_winding C (usym_hom Z Z (integer_mixed_left C g) h) (usym_hom Z Z (integer_mixed_left C h) g)
      (calc
         circle_winding C (usym_hom Z Z (integer_mixed_left C g) h)
         = int_mul (circle_winding C g) (circle_winding C h) by integer_mixed_winding C g h
         = int_mul (circle_winding C h) (circle_winding C g) by int_mul_comm (circle_winding C g) (circle_winding C h)
         = circle_winding C (usym_hom Z Z (integer_mixed_left C h) g)
           by inverse Int (circle_winding C (usym_hom Z Z (integer_mixed_left C h) g))
             (int_mul (circle_winding C h) (circle_winding C g)) (integer_mixed_winding C h g) ∎)

def integer_mixed_unit (C : CircleSignature)
  : Id (GroupHom (circle_group C) (circle_group C)) (integer_mixed_left C (C .loop)) (group_hom_id (circle_group C))
  ≔ let Z ≔ circle_group C in
    circle_hom_from_loop_agreement C Z (integer_mixed_left C (C .loop)) (group_hom_id Z)
      (concat (USym Z) (usym_hom Z Z (integer_mixed_left C (C .loop)) (C .loop)) (C .loop)
        (usym_hom Z Z (group_hom_id Z) (C .loop))
        (circle_group_hom_from_symmetry_loop C Z (C .loop))
        (inverse (USym Z) (usym_hom Z Z (group_hom_id Z) (C .loop)) (C .loop) (circle_group_hom_ev_identity C)))

{` ev(ℓ_g ∘ ℓ_h) = (ℓ_g)(h). `}
def integer_mixed_compose_loop (C : CircleSignature) (g h : USym (circle_group C))
  : Id (USym (circle_group C))
      (usym_hom (circle_group C) (circle_group C)
        (group_hom_compose (circle_group C) (circle_group C) (circle_group C) (integer_mixed_left C h) (integer_mixed_left C g))
        (C .loop))
      (usym_hom (circle_group C) (circle_group C) (integer_mixed_left C g) h)
  ≔ let Z ≔ circle_group C in let U ≔ USym Z in
    concat U
      (usym_hom Z Z (group_hom_compose Z Z Z (integer_mixed_left C h) (integer_mixed_left C g)) (C .loop))
      (usym_hom Z Z (integer_mixed_left C g) (usym_hom Z Z (integer_mixed_left C h) (C .loop)))
      (usym_hom Z Z (integer_mixed_left C g) h)
      (refl ((φ ↦ φ (C .loop)) : (U → U) → U) (usym_hom_compose Z Z Z (integer_mixed_left C h) (integer_mixed_left C g)))
      (refl (usym_hom Z Z (integer_mixed_left C g)) (circle_group_hom_from_symmetry_loop C Z h))

def integer_mixed_assoc (C : CircleSignature) (g h : USym (circle_group C))
  : Id (GroupHom (circle_group C) (circle_group C))
      (group_hom_compose (circle_group C) (circle_group C) (circle_group C) (integer_mixed_left C h) (integer_mixed_left C g))
      (group_hom_compose (circle_group C) (circle_group C) (circle_group C) (integer_mixed_left C g) (integer_mixed_left C h))
  ≔ let Z ≔ circle_group C in let U ≔ USym Z in
    circle_hom_from_loop_agreement C Z
      (group_hom_compose Z Z Z (integer_mixed_left C h) (integer_mixed_left C g))
      (group_hom_compose Z Z Z (integer_mixed_left C g) (integer_mixed_left C h))
      (calc
         usym_hom Z Z (group_hom_compose Z Z Z (integer_mixed_left C h) (integer_mixed_left C g)) (C .loop)
         = usym_hom Z Z (integer_mixed_left C g) h by integer_mixed_compose_loop C g h
         = usym_hom Z Z (integer_mixed_left C h) g by integer_mixed_coherence C g h
         = usym_hom Z Z (group_hom_compose Z Z Z (integer_mixed_left C g) (integer_mixed_left C h)) (C .loop)
           by inverse U (usym_hom Z Z (group_hom_compose Z Z Z (integer_mixed_left C g) (integer_mixed_left C h)) (C .loop))
             (usym_hom Z Z (integer_mixed_left C h) g) (integer_mixed_compose_loop C h g) ∎)

def integer_mixed_ring (C : CircleSignature) : MixedRing
  ≔ (circle_group C, C .loop, integer_mixed_left C, integer_mixed_left C,
     ((integer_mixed_unit C, integer_mixed_unit C), (integer_mixed_coherence C, integer_mixed_assoc C)))

def integer_mixed_ring_commutative (C : CircleSignature) : IsCommutativeMixedRing (integer_mixed_ring C)
  ≔ refl (integer_mixed_left C)

def integer_mixed_ring_non_trivial (C : CircleSignature) : IsNonTrivialMixedRing (integer_mixed_ring C)
  ≔ p ↦ circle_loop_not_refl C p

{` Litmus: in the induced abstract ring on USym ℤ the product of loop² and
   loop³ has winding number 6 (= 2 · 3). `}
def integer_mixed_two_times_three (C : CircleSignature)
  : Id Int (circle_winding C (mixed_mul (integer_mixed_ring C) (circle_power C (pos. 2)) (circle_power C (pos. 3))))
      (pos. 6)
  ≔ calc
      circle_winding C (mixed_mul (integer_mixed_ring C) (circle_power C (pos. 2)) (circle_power C (pos. 3)))
      = int_mul (circle_winding C (circle_power C (pos. 2))) (circle_winding C (circle_power C (pos. 3)))
        by integer_mixed_winding C (circle_power C (pos. 2)) (circle_power C (pos. 3))
      = int_mul (pos. 2) (pos. 3) by refl int_mul (circle_winding_power C (pos. 2)) (circle_winding_power C (pos. 3))
      = pos. 6 by refl (pos. 6 : Int) ∎

{` Footnote to the example: for m ≥ 0 the map classifying ℓ_{loop^m} is the
   degree-m map of def:dgm-map (module 80), by definition. `}
def integer_mixed_left_degree_map (C : CircleSignature) (m : Nat)
  : Id (C .carrier → C .carrier)
      (hom_function (circle_group C) (circle_group C) (integer_mixed_left C (circle_power C (pos. m))))
      (circle_degree_map C m)
  ≔ refl (circle_degree_map C m)
