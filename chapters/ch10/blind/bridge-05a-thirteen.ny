export "05-examples"
export "bridge-01-finite-groups"
export "../../../src/1003-finite-sum-congruences"
export "../../../src/1022-gset-orbit-partition"
export "../../../src/1013-sylow-example-tools"
export "../../../src/520-orbit-relations"
export "../../../src/522-orbit-fibers"

{` Bridges for the example at fingp.tex:16 (13 elements, orbits of
   cardinality dividing 8 ⇒ a fixed point). The blind statement is about an
   arbitrary group G; ours is the finite-family form
   (fingp_thirteen_eight_has_singleton). The bridge: X(sh_G) is the sum of the
   underlying sets of the orbits (orbit_splitting_members_equiv, chapter 5);
   since every orbit is a finite subset of the finite set X(sh_G), equality
   of orbits is decidable, so X/G is finite (surjective image of X(sh_G));
   our lemma gives an orbit with one element, and a transitive G-set whose
   underlying set is contractible has a fixed point (BG is connected). The
   parenthetical (|G| = 8 ⇒ orbit sizes divide 8) is gset_orbit_card_divides
   transported to the blind orbits. `}

def bridge_orbit_path_point (G : Group) (X : GSet G) (O : Orbits G X) (w : BlindOrbitSet G X O)
  : Id (Orbits G X) O (orbit_of_point G X (w .fst))
  ≔ orbit_member_path_equiv G X O (shape G, w .fst) .map (w .snd)

def bridge_orbits_decidable (G : Group) (X : GSet G) (hX : IsFinite (gset_underlying G X))
  (hO : (O : Orbits G X) → IsFinite (BlindOrbitSet G X O)) : DecidableEquality (Orbits G X)
  ≔ O O' ↦
    let U ≔ gset_underlying G X in
    let A ≔ Orbits G X in
    let D ≔ Decidable (Id A O O') in
    let dU ≔ finite_decidable_equality U hX in
    mere_rec (Σ (gset_underlying G (gsubset_gset G X (O' .fst)))
        (x ↦ (y : gset_underlying G (gsubset_gset G X (O' .fst))) →
          Mere (Σ (USym G) (g ↦ Id (gset_underlying G (gsubset_gset G X (O' .fst))) x
            (gset_usym_act G (gsubset_gset G X (O' .fst)) g y)))))
      D (decidability_prop (Id A O O') (orbits_set G X O O'))
      (t ↦
        let w ≔ t .fst in
        let x ≔ w .fst in
        let q' ≔ bridge_orbit_path_point G X O' w in
        match finite_subset_decidable U dU (y ↦ O .fst (shape G) y .fst) (y ↦ O .fst (shape G) y .snd) (hO O) x [
        | inl. m ↦ inl. (concat A O (orbit_of_point G X x) O'
                          (orbit_member_path_equiv G X O (shape G, x) .map m)
                          (inverse A O' (orbit_of_point G X x) q'))
        | inr. nm ↦ inr. (q ↦ nm (equiv_inverse_map (OrbitMember G X O (shape G, x)) (Id A O (orbit_of_point G X x))
                            (orbit_member_path_equiv G X O (shape G, x)) (concat A O O' (orbit_of_point G X x) q q'))) ])
      (O' .snd)

def bridge_orbits_finite (G : Group) (X : GSet G) (hX : IsFinite (gset_underlying G X))
  (hO : (O : Orbits G X) → IsFinite (BlindOrbitSet G X O)) : IsFinite (Orbits G X)
  ≔ let U ≔ gset_underlying G X in
    let A ≔ Orbits G X in
    finite_surjection_target U A hX (bridge_orbits_decidable G X hX hO) (orbit_of_point G X)
      (O ↦ mere_rec (Σ (gset_underlying G (gsubset_gset G X (O .fst)))
            (x ↦ (y : gset_underlying G (gsubset_gset G X (O .fst))) →
              Mere (Σ (USym G) (g ↦ Id (gset_underlying G (gsubset_gset G X (O .fst))) x
                (gset_usym_act G (gsubset_gset G X (O .fst)) g y)))))
          (Mere (BookFiber U A (orbit_of_point G X) O)) (mere_isprop (BookFiber U A (orbit_of_point G X) O))
          (t ↦ mere (BookFiber U A (orbit_of_point G X) O) (t .fst .fst, bridge_orbit_path_point G X O (t .fst)))
          (O .snd))

{` A G-set whose underlying set X(sh_G) is contractible has a fixed point. `}
def bridge_contractible_gset_fixed (G : Group) (Y : GSet G) (c : BookIsContr (gset_underlying G Y))
  : BlindFixedPoints G Y
  ≔ z ↦ connected_based_elim native_truncation (BG G .carrier) (bg_connected G) (shape G)
          (w ↦ BookIsContr (Y w .fst)) (w ↦ book_iscontr_isprop (Y w .fst)) c z .center

def bridge_example_thirteen : blind_example_thirteen
  ≔ G X hc hO ↦
    let U ≔ gset_underlying G X in
    let A ≔ Orbits G X in
    let P : A → Type ≔ O ↦ BlindOrbitSet G X O in
    let hX ≔ hc .fst in
    let eS ≔ orbit_splitting_members_equiv G X in
    let hS : IsFinite (Σ A P) ≔ finite_of_equiv (Σ A P) U eS hX in
    let c13 ≔ concat Nat (cardinality (Σ A P) hS) (cardinality U hX) 13 (cardinality_equiv (Σ A P) U eS hS hX) (hc .snd) in
    let hA ≔ bridge_orbits_finite G X hX (O ↦ hO O .fst) in
    mere_rec (Σ A (O ↦ Id Nat (cardinality (P O) (hO O .fst)) (suc. zero.))) (Mere (BlindFixedPoints G X))
      (mere_isprop (BlindFixedPoints G X))
      (u ↦
        let O ≔ u .fst in
        let Y ≔ gsubset_gset G X (O .fst) in
        mere_rec (P O) (Mere (BlindFixedPoints G X)) (mere_isprop (BlindFixedPoints G X))
          (p0 ↦ mere (BlindFixedPoints G X)
             (z ↦ bridge_contractible_gset_fixed G Y (p0, q ↦ fingp_card_one_eq (P O) (hO O .fst) (u .snd) p0 q) z .fst))
          (finite_card_nonzero_inhabited (P O) (hO O .fst)
             (e ↦ nat_zero_ne_suc zero. (concat Nat zero. (cardinality (P O) (hO O .fst)) (suc. zero.)
                    (inverse Nat (cardinality (P O) (hO O .fst)) zero. e) (u .snd)))))
      (fingp_thirteen_eight_has_singleton A hA P (O ↦ hO O .fst) hS (O ↦ hO O .snd) c13)

{` The parenthetical: if |G| = 8, every orbit of a finite G-set is finite of
   cardinality dividing 8 (the orbit through any of its points, module 1022). `}
def bridge_orbit_set_point (G : Group) (X : GSet G) (x : gset_underlying G X)
  : Id Type (BlindOrbitSet G X (orbit_of_point G X x)) (GSetOrbitSet G X x)
  ≔ refl (GSetOrbitSet G X x)

def bridge_example_thirteen_orbits_divide : blind_example_thirteen_orbits_divide
  ≔ G hG X hX O ↦
    let P : Orbits G X → Type ≔ O' ↦ BlindOrbitSet G X O' in
    let C : Orbits G X → Type ≔ O' ↦ Σ (IsFinite (P O')) (h ↦ NatDivides (cardinality (P O') h) 8) in
    let hC : (O' : Orbits G X) → isProp (C O')
      ≔ O' ↦ sigma_prop (IsFinite (P O')) (h ↦ NatDivides (cardinality (P O') h) 8) (isfinite_prop (P O'))
               (h ↦ mere_isprop (Σ Nat (q ↦ Id Nat 8 (mul q (cardinality (P O') h))))) in
    mere_rec (Σ (gset_underlying G (gsubset_gset G X (O .fst)))
        (x ↦ (y : gset_underlying G (gsubset_gset G X (O .fst))) →
          Mere (Σ (USym G) (g ↦ Id (gset_underlying G (gsubset_gset G X (O .fst))) x
            (gset_usym_act G (gsubset_gset G X (O .fst)) g y)))))
      (C O) (hC O)
      (t ↦
        let x ≔ t .fst .fst in
        transport (Orbits G X) C (orbit_of_point G X x) O
          (inverse (Orbits G X) O (orbit_of_point G X x) (bridge_orbit_path_point G X O (t .fst)))
          (gset_orbit_set_finite G (hG .fst) X hX x,
           transport Nat (NatDivides (cardinality (GSetOrbitSet G X x) (gset_orbit_set_finite G (hG .fst) X hX x)))
             (group_card G (hG .fst)) 8 (hG .snd) (gset_orbit_card_divides G (hG .fst) X hX x)))
      (O .snd)
