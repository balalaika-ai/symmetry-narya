export "bridge-05b-sigma-small"
export "../../../src/1017-sigma-six-sylow-count"
export "../../../src/1052-sigma-n-order-three-classes"

{` Bridges for the counting claims of the example at fingp.tex:27.

   Refuted literal claims (counterexamples by counting mod 3):
   - "Σ_n has n(n-1)(n-2)/6 subgroups of order 3": for n = 6 this says 20,
     but the number of subgroups of order 3 of a group of order divisible by
     3 is ≡ 1 (mod 3) (module 1051), and 20 ≢ 1;
   - "10 subgroups of order 9, one for each 3-element subset": there are
     binomial(6,3) = 20 such subsets, but the number of 3-Sylow subgroups of
     Σ_6 is ≡ 1 (mod 3) (thm:sylow3, module 1017).
   Corrected variants: the formula for n = 3, 4 is proved (1 and 4); the
   counts for n = 5 (10) and n = 6 (40, 10 of order 9) are not formalized. `}

def bridge_twenty_not_one_mod_three (h : NatCongruent 3 20 1) : Empty
  ≔ nat_decision_false_reflect (NatDivides 3 19) (nat_divides_decidable_any 3 19) (refl (false. : Bool))
      (fingp_congruent_divides_diff 3 20 1 19 (refl (20 : Nat)) h)

def bridge_three_divides_sigma6 : NatDivides 3 (group_card (symmetric_group 6) (symmetric_group_finite 6))
  ≔ transport Nat (NatDivides 3) (mul (mul two (factorial 5)) three) (group_card (symmetric_group 6) (symmetric_group_finite 6))
      (inverse Nat (group_card (symmetric_group 6) (symmetric_group_finite 6)) (mul (mul two (factorial 5)) three)
        (concat Nat (group_card (symmetric_group 6) (symmetric_group_finite 6)) (factorial 6) (mul (mul two (factorial 5)) three)
          (symmetric_group_card 6) sigma6_factorial_split))
      (mere (Σ Nat (q ↦ Id Nat (mul (mul two (factorial 5)) three) (mul q 3))) (mul two (factorial 5), refl (mul (mul two (factorial 5)) three)))

{` Σ_6 does not have exactly 20 subgroups of order 3. `}
def bridge_sigma6_order3_not_twenty (h : IsFinite (FiniteOrderSubgroups (symmetric_group 6) 3))
  (e : Id Nat (cardinality (FiniteOrderSubgroups (symmetric_group 6) 3) h) 20) : Empty
  ≔ bridge_twenty_not_one_mod_three
      (transport Nat (x ↦ NatCongruent 3 x 1) (cardinality (FiniteOrderSubgroups (symmetric_group 6) 3) h) 20 e
        (order_p_subgroups_congruent 2 nat_prime_three (symmetric_group 6) (symmetric_group_finite 6) bridge_three_divides_sigma6 h))

def bridge_sigman_order3_count_refuted (h : blind_sigman_order3_count) : Empty
  ≔ let w ≔ h 3 in
    let k20 : Id Nat (w .fst) 20 ≔ fingp_mul_cancel_left 6 (w .fst) 20 star. (w .snd .fst) in
    bridge_sigma6_order3_not_twenty (w .snd .snd .fst)
      (concat Nat (cardinality (FiniteOrderSubgroups (symmetric_group 6) 3) (w .snd .snd .fst)) (w .fst) 20 (w .snd .snd .snd) k20)

{` The corrected formula for n = 3 and n = 4. `}
def bridge_sigman_order3_count_three
  : Σ Nat (k ↦ Product (Id Nat (mul 6 k) (mul (mul (add 0 3) (add 0 2)) (add 0 1)))
                       (BlindHasCard (BlindSubgroupsOfOrder (symmetric_group (add 0 3)) 3) k))
  ≔ let A ≔ FiniteOrderSubgroups (symmetric_group 3) 3 in
    let e ≔ fingp_contractible_fin_one_equiv A bridge_sigma3_unique_order3 in
    let hA ≔ finite_of_equiv A (Fin 1) e (fin_is_finite 1) in
    (1, (refl (6 : Nat), (hA, cardinality_equiv A (Fin 1) e hA (fin_is_finite 1))))

def bridge_sigman_order3_count_four
  : Σ Nat (k ↦ Product (Id Nat (mul 6 k) (mul (mul (add 1 3) (add 1 2)) (add 1 1)))
                       (BlindHasCard (BlindSubgroupsOfOrder (symmetric_group (add 1 3)) 3) k))
  ≔ (4, (refl (24 : Nat), bridge_sigma4_order3_count))

{` The 3-element subsets of Fin 6: there are 20. `}
def bridge_triples_equiv : Equiv BlindTripleSubsets (BoolSubsets 6 3)
  ≔ family_equiv (Fin 6 → Bool) (A ↦ BlindHasCard (Σ (Fin 6) (x ↦ Id Bool (A x) true.)) 3) (A ↦ Id Nat (true_count 6 A) 3)
      (A ↦ let C ≔ Σ (Fin 6) (x ↦ Id Bool (A x) true.) in
        iff_equiv (BlindHasCard C 3) (Id Nat (true_count 6 A) 3)
          (sigma_prop (IsFinite C) (h ↦ Id Nat (cardinality C h) 3) (isfinite_prop C) (h ↦ nat_set (cardinality C h) 3))
          (nat_set (true_count 6 A) 3)
          (u ↦ concat Nat (true_count 6 A) (cardinality C (u .fst)) 3
                 (inverse Nat (cardinality C (u .fst)) (true_count 6 A)
                   (cardinality_equiv C (Fin (true_count 6 A)) (bool_carrier_fin 6 A) (u .fst) (fin_is_finite (true_count 6 A))))
                 (u .snd))
          (c ↦ let hC ≔ finite_of_equiv C (Fin (true_count 6 A)) (bool_carrier_fin 6 A) (fin_is_finite (true_count 6 A)) in
               (hC, concat Nat (cardinality C hC) (true_count 6 A) 3
                      (cardinality_equiv C (Fin (true_count 6 A)) (bool_carrier_fin 6 A) hC (fin_is_finite (true_count 6 A))) c)))

def bridge_triples_fin : Equiv BlindTripleSubsets (Fin 20)
  ≔ compose_equiv BlindTripleSubsets (BoolSubsets 6 3) (Fin 20) bridge_triples_equiv (bool_subsets_fin 6 3)

def bridge_sigma6_order9_sylow : Equiv (FiniteOrderSubgroups (symmetric_group 6) 9) (SylowSubgroups 3 (symmetric_group 6))
  ≔ bridge_order_sylow_equiv 3 (symmetric_group 6) (symmetric_group_finite 6) 2 (factorial 6) (symmetric_group_card 6)
      sigma6_largest_three

{` "One subgroup of order 9 for each 3-element subset" is refuted. `}
def bridge_sigma6_order9_per_triple_refuted (h : blind_sigma6_order9_per_triple) : Empty
  ≔ let T ≔ BlindTripleSubsets in
    let Y ≔ SylowSubgroups 3 (symmetric_group 6) in
    mere_rec (Equiv T (FiniteOrderSubgroups (symmetric_group 6) 9)) Empty empty_prop
      (e ↦
        let eY ≔ compose_equiv T (FiniteOrderSubgroups (symmetric_group 6) 9) Y e bridge_sigma6_order9_sylow in
        let hT ≔ finite_of_equiv T (Fin 20) bridge_triples_fin (fin_is_finite 20) in
        let hY ≔ finite_of_equiv Y T (canonical_inverse_equiv T Y eY) hT in
        let cY : Id Nat (cardinality Y hY) 20
          ≔ concat Nat (cardinality Y hY) (cardinality T hT) 20 (cardinality_equiv Y T (canonical_inverse_equiv T Y eY) hY hT)
              (cardinality_equiv T (Fin 20) bridge_triples_fin hT (fin_is_finite 20)) in
        let Q ≔ eY .map (equiv_inverse_map T (Fin 20) bridge_triples_fin (inr. star.)) in
        bridge_twenty_not_one_mod_three
          (transport Nat (x ↦ NatCongruent 3 x 1) (cardinality Y hY) 20 cY (sigma6_sylow_count_at Q hY .snd)))
      h

{` For n > 5 the subgroups of order 3 are not all conjugate (module 1052:
   ⟨(0 1 2)⟩ and ⟨(0 1 2)(3 4 5)⟩ in Σ_(m+6)). `}
def bridge_sigman_order3_not_all_conjugate : blind_sigman_order3_not_all_conjugate
  ≔ m all ↦ sigma_n_order_three_not_all_conjugate m
      (S T ↦ bridge_conjugate_to (symmetric_group (add m 6)) (S .fst) (T .fst) (all S T))
