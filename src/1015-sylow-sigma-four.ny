export "1014-sylow-sigma-three"

{` Chapter 10, the example at fingp.tex 27–33, second paragraph: for Σ_4,
   |Σ_4| = 24 = 8·3 and the Sylow theorems give that the number of
   subgroups of order 3 (the 3-Sylow subgroups, 3^1 being the largest power
   of 3 dividing 24) is 1 or 4 (it divides 8 and is ≡ 1 mod 3), and that
   they are all conjugate (thm:sylow2). The subgroup ⟨(0 1 2)⟩ (the
   book's H ⊆ Σ_3 viewed in Σ_4; here given directly as the cyclic subgroup
   of the 3-cycle (0 1 2) of Fin 4 rather than as the image of H under the
   inclusion Σ_3 → Σ_4) is not normal, so there are exactly 4.

   Non-normality: ⟨(0 1 2)⟩ ≠ ⟨(1 2 3)⟩, since (0 1 2) is in the first but
   not in the second (every power of (1 2 3) fixes 0, while (0 1 2) moves
   it; decided by computation on Fin 4). Both are 3-Sylow, hence conjugate;
   a normal subgroup equals all its conjugates. `}

def fin4_zero : Fin (suc. three) ≔ inr. star.
def fin4_one : Fin (suc. three) ≔ inl. (inr. star.)

{` The 3-cycles (0 1 2) and (1 2 3) of Fin 4. `}
def fin4_cycle012 : Fin (suc. three) → Fin (suc. three) ≔ [
  | inr. u ↦ inl. (inr. u)
  | inl. (inr. u) ↦ inl. (inl. (inr. u))
  | inl. (inl. (inr. u)) ↦ inr. u
  | inl. (inl. (inl. x)) ↦ inl. (inl. (inl. x)) ]

def fin4_cycle123 : Fin (suc. three) → Fin (suc. three) ≔ [
  | inr. u ↦ inr. u
  | inl. (inr. u) ↦ inl. (inl. (inr. u))
  | inl. (inl. (inr. u)) ↦ inl. (inl. (inl. (inr. u)))
  | inl. (inl. (inl. (inr. u))) ↦ inl. (inr. u)
  | inl. (inl. (inl. (inl. e))) ↦ match e [] ]

def fin4_cycle012_cube : (x : Fin (suc. three)) → Id (Fin (suc. three)) (fin4_cycle012 (fin4_cycle012 (fin4_cycle012 x))) x
  ≔ decision_bool_reflect ((x : Fin (suc. three)) → Id (Fin (suc. three)) (fin4_cycle012 (fin4_cycle012 (fin4_cycle012 x))) x)
      (fin_forall_decidable (suc. three) (x ↦ Id (Fin (suc. three)) (fin4_cycle012 (fin4_cycle012 (fin4_cycle012 x))) x)
        (x ↦ fin_decidable_equality (suc. three) (fin4_cycle012 (fin4_cycle012 (fin4_cycle012 x))) x))
      (refl (true. : Bool))

def fin4_cycle123_cube : (x : Fin (suc. three)) → Id (Fin (suc. three)) (fin4_cycle123 (fin4_cycle123 (fin4_cycle123 x))) x
  ≔ decision_bool_reflect ((x : Fin (suc. three)) → Id (Fin (suc. three)) (fin4_cycle123 (fin4_cycle123 (fin4_cycle123 x))) x)
      (fin_forall_decidable (suc. three) (x ↦ Id (Fin (suc. three)) (fin4_cycle123 (fin4_cycle123 (fin4_cycle123 x))) x)
        (x ↦ fin_decidable_equality (suc. three) (fin4_cycle123 (fin4_cycle123 (fin4_cycle123 x))) x))
      (refl (true. : Bool))

def fin4_one_ne_zero : Not (Id (Fin (suc. three)) fin4_one fin4_zero)
  ≔ nat_decision_false_reflect (Id (Fin (suc. three)) fin4_one fin4_zero)
      (fin_decidable_equality (suc. three) fin4_one fin4_zero) (refl (false. : Bool))

def sigma4_cycle012 : USym (symmetric_group (suc. three))
  ≔ permutation_symmetry (standard_set (suc. three)) (perm3_equiv (Fin (suc. three)) fin4_cycle012 fin4_cycle012_cube)

def sigma4_cycle123 : USym (symmetric_group (suc. three))
  ≔ permutation_symmetry (standard_set (suc. three)) (perm3_equiv (Fin (suc. three)) fin4_cycle123 fin4_cycle123_cube)

def sigma4_cycle012_cube
  : Id (USym (symmetric_group (suc. three))) (usym_power (symmetric_group (suc. three)) sigma4_cycle012 (suc. (suc. (suc. zero.))))
      (usym_unit (symmetric_group (suc. three)))
  ≔ perm3_symmetry_cube (standard_set (suc. three)) fin4_cycle012 fin4_cycle012_cube

def sigma4_cycle123_cube
  : Id (USym (symmetric_group (suc. three))) (usym_power (symmetric_group (suc. three)) sigma4_cycle123 (suc. (suc. (suc. zero.))))
      (usym_unit (symmetric_group (suc. three)))
  ≔ perm3_symmetry_cube (standard_set (suc. three)) fin4_cycle123 fin4_cycle123_cube

def sigma4_cycle012_ne : Not (Id (USym (symmetric_group (suc. three))) sigma4_cycle012 (usym_unit (symmetric_group (suc. three))))
  ≔ perm_symmetry_ne_unit (standard_set (suc. three)) (perm3_equiv (Fin (suc. three)) fin4_cycle012 fin4_cycle012_cube) fin4_zero
      fin4_one_ne_zero

def sigma4_cycle123_ne : Not (Id (USym (symmetric_group (suc. three))) sigma4_cycle123 (usym_unit (symmetric_group (suc. three))))
  ≔ perm_symmetry_ne_unit (standard_set (suc. three)) (perm3_equiv (Fin (suc. three)) fin4_cycle123 fin4_cycle123_cube) fin4_one
      (nat_decision_false_reflect (Id (Fin (suc. three)) (fin4_cycle123 fin4_one) fin4_one)
        (fin_decidable_equality (suc. three) (fin4_cycle123 fin4_one) fin4_one) (refl (false. : Bool)))

{` The subgroups P = ⟨(0 1 2)⟩ and Q = ⟨(1 2 3)⟩ of Σ_4; both are 3-Sylow. `}
def sigma4_sylow_p : Subgroups (symmetric_group (suc. three))
  ≔ cyclic_prime_subgroup (suc. (suc. zero.)) nat_prime_three (symmetric_group (suc. three)) sigma4_cycle012
      sigma4_cycle012_cube sigma4_cycle012_ne

def sigma4_sylow_q : Subgroups (symmetric_group (suc. three))
  ≔ cyclic_prime_subgroup (suc. (suc. zero.)) nat_prime_three (symmetric_group (suc. three)) sigma4_cycle123
      sigma4_cycle123_cube sigma4_cycle123_ne

def sigma4_largest_three
  : IsLargestPrimePower (suc. (suc. (suc. zero.))) (suc. zero.) (factorial (suc. three))
  ≔ fingp_largest_power_decide (suc. (suc. (suc. zero.))) (suc. zero.) (factorial (suc. three))
      (refl (true. : Bool)) (refl (false. : Bool))

def sigma4_sylow_p_is_sylow : IsSylowSubgroup (suc. (suc. (suc. zero.))) (symmetric_group (suc. three)) sigma4_sylow_p
  ≔ cyclic_prime_sylow (suc. (suc. zero.)) nat_prime_three (symmetric_group (suc. three)) (symmetric_group_finite (suc. three))
      sigma4_cycle012 sigma4_cycle012_cube sigma4_cycle012_ne (factorial (suc. three)) (symmetric_group_card (suc. three))
      sigma4_largest_three

def sigma4_sylow_q_is_sylow : IsSylowSubgroup (suc. (suc. (suc. zero.))) (symmetric_group (suc. three)) sigma4_sylow_q
  ≔ cyclic_prime_sylow (suc. (suc. zero.)) nat_prime_three (symmetric_group (suc. three)) (symmetric_group_finite (suc. three))
      sigma4_cycle123 sigma4_cycle123_cube sigma4_cycle123_ne (factorial (suc. three)) (symmetric_group_card (suc. three))
      sigma4_largest_three

{` (0 1 2) ∈ P, (0 1 2) ∉ Q, hence P ≠ Q. `}
def sigma4_cycle012_in_p
  : Id (gset_underlying (symmetric_group (suc. three)) (sigma4_sylow_p .gset))
      (gset_usym_act (symmetric_group (suc. three)) (sigma4_sylow_p .gset) sigma4_cycle012 (sigma4_sylow_p .point))
      (sigma4_sylow_p .point)
  ≔ let G ≔ symmetric_group (suc. three) in
    let X ≔ sigma4_sylow_p .gset in
    transport (USym G) (t ↦ Id (gset_underlying G X) (gset_usym_act G X t (sigma4_sylow_p .point)) (sigma4_sylow_p .point))
      (usym_power G sigma4_cycle012 (suc. zero.)) sigma4_cycle012 (usym_power_one G sigma4_cycle012)
      (cyclic_subgroup_power_member (suc. (suc. zero.)) G sigma4_cycle012 sigma4_cycle012_cube
        (prime_order_powers_nontrivial (suc. (suc. (suc. zero.))) nat_prime_three G sigma4_cycle012 sigma4_cycle012_cube
          sigma4_cycle012_ne)
        (suc. zero.))

def sigma4_cycle123_powers_fix_zero (k : Nat)
  : Id (Fin (suc. three)) (permutation_action (standard_set (suc. three)) (usym_power (symmetric_group (suc. three)) sigma4_cycle123 k) fin4_zero)
      fin4_zero
  ≔ concat (Fin (suc. three))
      (permutation_action (standard_set (suc. three)) (usym_power (symmetric_group (suc. three)) sigma4_cycle123 k) fin4_zero)
      (iterate (Fin (suc. three)) fin4_cycle123 k fin4_zero) fin4_zero
      (perm_symmetry_power_action (standard_set (suc. three)) (perm3_equiv (Fin (suc. three)) fin4_cycle123 fin4_cycle123_cube) k fin4_zero)
      (cauchy_iterate_fixed (Fin (suc. three)) fin4_cycle123 fin4_zero (refl fin4_zero) k)

def sigma4_cycle012_not_power (k : Nat)
  (e : Id (USym (symmetric_group (suc. three))) sigma4_cycle012 (usym_power (symmetric_group (suc. three)) sigma4_cycle123 k))
  : Empty
  ≔ fin4_one_ne_zero
      (concat (Fin (suc. three)) fin4_one
        (permutation_action (standard_set (suc. three)) (usym_power (symmetric_group (suc. three)) sigma4_cycle123 k) fin4_zero)
        fin4_zero
        (refl ((t ↦ permutation_action (standard_set (suc. three)) t fin4_zero) : USym (symmetric_group (suc. three)) → Fin (suc. three)) e)
        (sigma4_cycle123_powers_fix_zero k))

def sigma4_sylow_p_ne_q (e : Id (Subgroups (symmetric_group (suc. three))) sigma4_sylow_p sigma4_sylow_q) : Empty
  ≔ let G ≔ symmetric_group (suc. three) in
    let inq ≔ transport (Subgroups G)
      (S ↦ Id (gset_underlying G (S .gset)) (gset_usym_act G (S .gset) sigma4_cycle012 (S .point)) (S .point))
      sigma4_sylow_p sigma4_sylow_q e sigma4_cycle012_in_p in
    mere_rec (Σ Nat (k ↦ Product (BookLt k (suc. (suc. (suc. zero.)))) (Id (USym G) sigma4_cycle012 (usym_power G sigma4_cycle123 k))))
      Empty empty_prop
      (w ↦ sigma4_cycle012_not_power (w .fst) (w .snd .snd))
      (cyclic_subgroup_member_power (suc. (suc. zero.)) G sigma4_cycle123 sigma4_cycle123_cube
        (prime_order_powers_nontrivial (suc. (suc. (suc. zero.))) nat_prime_three G sigma4_cycle123 sigma4_cycle123_cube
          sigma4_cycle123_ne)
        sigma4_cycle012 inq)

{` thm:sylow2 here: P and Q are conjugate; P is not normal. `}
def sigma4_sylow_conjugate
  : Mere (Σ (USym (symmetric_group (suc. three)))
      (g ↦ Id (Subgroups (symmetric_group (suc. three))) (subgroup_conjugate (symmetric_group (suc. three)) g sigma4_sylow_p) sigma4_sylow_q))
  ≔ sylow_subgroups_conjugate (suc. (suc. (suc. zero.))) nat_prime_three (symmetric_group (suc. three)) sigma4_sylow_p sigma4_sylow_q
      sigma4_sylow_p_is_sylow sigma4_sylow_q_is_sylow

def sigma4_sylow_p_not_normal (n : IsNormalSubgroup (symmetric_group (suc. three)) sigma4_sylow_p) : Empty
  ≔ let G ≔ symmetric_group (suc. three) in
    mere_rec (Σ (USym G) (g ↦ Id (Subgroups G) (subgroup_conjugate G g sigma4_sylow_p) sigma4_sylow_q)) Empty empty_prop
      (w ↦ sigma4_sylow_p_ne_q
        (concat (Subgroups G) sigma4_sylow_p (subgroup_conjugate G (w .fst) sigma4_sylow_p) sigma4_sylow_q
          (inverse (Subgroups G) (subgroup_conjugate G (w .fst) sigma4_sylow_p) sigma4_sylow_p
            (normal_subgroup_fixed G sigma4_sylow_p n (w .fst)))
          (w .snd)))
      sigma4_sylow_conjugate

{` Counting: |Syl_3(Σ_4)| divides 8 and is ≡ 1 mod 3, so it is 1 or 4. `}
def fingp_eight_not_one_mod_three
  (h : NatCongruent (suc. (suc. (suc. zero.))) (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. zero.)))))))) (suc. zero.)) : Empty
  ≔ nat_decision_false_reflect (NatDivides (suc. (suc. (suc. zero.))) (suc. (suc. (suc. (suc. (suc. (suc. (suc. zero.))))))))
      (nat_divides_decidable_any (suc. (suc. (suc. zero.))) (suc. (suc. (suc. (suc. (suc. (suc. (suc. zero.))))))))
      (refl (false. : Bool))
      (fingp_congruent_divides_diff (suc. (suc. (suc. zero.))) (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. zero.))))))))
        (suc. zero.) (suc. (suc. (suc. (suc. (suc. (suc. (suc. zero.))))))) (refl (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. zero.))))))) : Nat)) h)

def fingp_divisor_eight_cases (d : Nat) (k : Nat)
  : Le k (suc. (suc. (suc. zero.))) → Id Nat d (nat_power (suc. (suc. zero.)) k)
    → NatCongruent (suc. (suc. (suc. zero.))) d (suc. zero.)
    → Sum (Id Nat d (suc. zero.)) (Id Nat d (suc. (suc. (suc. (suc. zero.)))))
  ≔ match k [
  | zero. ↦ _ e _ ↦ inl. e
  | suc. zero. ↦ _ e c ↦ absurd (Sum (Id Nat d (suc. zero.)) (Id Nat d (suc. (suc. (suc. (suc. zero.))))))
      (fingp_two_not_one_mod_three
        (transport Nat (x ↦ NatCongruent (suc. (suc. (suc. zero.))) x (suc. zero.)) d (suc. (suc. zero.)) e c))
  | suc. (suc. zero.) ↦ _ e _ ↦ inr. e
  | suc. (suc. (suc. zero.)) ↦ _ e c ↦ absurd (Sum (Id Nat d (suc. zero.)) (Id Nat d (suc. (suc. (suc. (suc. zero.))))))
      (fingp_eight_not_one_mod_three
        (transport Nat (x ↦ NatCongruent (suc. (suc. (suc. zero.))) x (suc. zero.)) d
          (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. zero.)))))))) e c))
  | suc. (suc. (suc. (suc. k))) ↦ le _ _ ↦ match le [] ]

def sigma4_sylow_three_count_cases
  : Sum (Id Nat (cardinality (SylowSubgroups (suc. (suc. (suc. zero.))) (symmetric_group (suc. three)))
          (sylow_subgroups_finite (suc. (suc. (suc. zero.))) nat_prime_three (symmetric_group (suc. three)) sigma4_sylow_p
            sigma4_sylow_p_is_sylow)) (suc. zero.))
      (Id Nat (cardinality (SylowSubgroups (suc. (suc. (suc. zero.))) (symmetric_group (suc. three)))
          (sylow_subgroups_finite (suc. (suc. (suc. zero.))) nat_prime_three (symmetric_group (suc. three)) sigma4_sylow_p
            sigma4_sylow_p_is_sylow)) (suc. (suc. (suc. (suc. zero.)))))
  ≔ let p : Nat ≔ suc. (suc. (suc. zero.)) in
    let G ≔ symmetric_group (suc. three) in
    let P ≔ sigma4_sylow_p in
    let sP ≔ sigma4_sylow_p_is_sylow in
    let d ≔ cardinality (SylowSubgroups p G) (sylow_subgroups_finite p nat_prime_three G P sP) in
    let hP ≔ cyclic_prime_subgroup_finite (suc. (suc. zero.)) nat_prime_three G sigma4_cycle012 sigma4_cycle012_cube
      sigma4_cycle012_ne in
    let dv : NatDivides d (nat_power (suc. (suc. zero.)) (suc. (suc. (suc. zero.))))
      ≔ sylow_count_divides p nat_prime_three G P sP (symmetric_group_finite (suc. three)) hP
          (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. zero.)))))))) (suc. (suc. zero.))
          (symmetric_group_card (suc. three))
          (cyclic_prime_subgroup_card (suc. (suc. zero.)) nat_prime_three G sigma4_cycle012 sigma4_cycle012_cube
            sigma4_cycle012_ne hP) in
    let w ≔ prime_power_divisor (suc. (suc. zero.)) nat_prime_two (suc. (suc. (suc. zero.))) d dv in
    fingp_divisor_eight_cases d (w .fst) (w .snd .fst) (w .snd .snd) (sylow_three_congruence p nat_prime_three G P sP)

{` |Syl_3(Σ_4)| = 4. `}
def sigma4_sylow_three_count
  : Id Nat (cardinality (SylowSubgroups (suc. (suc. (suc. zero.))) (symmetric_group (suc. three)))
      (sylow_subgroups_finite (suc. (suc. (suc. zero.))) nat_prime_three (symmetric_group (suc. three)) sigma4_sylow_p
        sigma4_sylow_p_is_sylow)) (suc. (suc. (suc. (suc. zero.))))
  ≔ match sigma4_sylow_three_count_cases [
  | inl. e1 ↦ absurd (Id Nat (cardinality (SylowSubgroups (suc. (suc. (suc. zero.))) (symmetric_group (suc. three)))
        (sylow_subgroups_finite (suc. (suc. (suc. zero.))) nat_prime_three (symmetric_group (suc. three)) sigma4_sylow_p
          sigma4_sylow_p_is_sylow)) (suc. (suc. (suc. (suc. zero.)))))
      (sigma4_sylow_p_ne_q (inverse (Subgroups (symmetric_group (suc. three))) sigma4_sylow_q sigma4_sylow_p
        (sylow_card_one_unique (suc. (suc. (suc. zero.))) nat_prime_three (symmetric_group (suc. three)) sigma4_sylow_p
          sigma4_sylow_p_is_sylow e1 sigma4_sylow_q sigma4_sylow_q_is_sylow)))
  | inr. e4 ↦ e4 ]
