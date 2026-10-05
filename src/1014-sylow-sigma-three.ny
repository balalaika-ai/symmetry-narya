export "1013-sylow-example-tools"

{` Chapter 10, the example at fingp.tex 27–33, first paragraph: from
   |Σ_3| = 6 the Sylow theorems give that Σ_3 has a unique subgroup H with
   |H| = 3, which is therefore normal.

   H = ⟨(0 1 2)⟩ (cyclic_prime_subgroup of the 3-cycle, module 1011; it
   exists by Cauchy, here it is given explicitly). 3^1 is the largest power
   of 3 dividing 6 (decided by computation), so H is a 3-Sylow subgroup;
   thm:sylow3 gives |Syl_3(Σ_3)| | 2 and ≡ 1 (mod 3), hence = 1; every
   subgroup of order 3 is 3-Sylow, hence equal to H; and H is fixed by
   conjugation (conjugates of Sylow subgroups are Sylow), i.e. normal
   (normal_iff_fixed, module 903). `}

{` From thm:sylow3 (1): |G| = c·|P| gives |Syl_G^p| | c. `}
def sylow_count_divides (p : Nat) (hp : NatIsPrime p) (G : Group) (P : Subgroups G) (sP : IsSylowSubgroup p G P)
  (hG : IsFiniteGroup G) (hP : IsFiniteGroup (subgroup_group G P)) (c k : Nat)
  (hn : Id Nat (group_card G hG) (mul c (suc. k))) (hk : Id Nat (group_card (subgroup_group G P) hP) (suc. k))
  : NatDivides (cardinality (SylowSubgroups p G) (sylow_subgroups_finite p hp G P sP)) c
  ≔ let st ≔ sylow_three_divides p hp G P sP in
    let m ≔ st .fst in
    let hG' ≔ sylow_group_finite p G P sP in
    let hP' ≔ sylow_subgroup_finite p G P sP in
    let cP : Id Nat (group_card (subgroup_group G P) hP') (suc. k)
      ≔ concat Nat (group_card (subgroup_group G P) hP') (group_card (subgroup_group G P) hP) (suc. k)
          (fingp_group_card_irrel (subgroup_group G P) hP' hP) hk in
    let mc : Id Nat m c
      ≔ nat_mul_cancel_right k m c
          (calc
            mul m (suc. k) = mul m (group_card (subgroup_group G P) hP')
              by refl (mul m) (inverse Nat (group_card (subgroup_group G P) hP') (suc. k) cP)
            = group_card G hG' by inverse Nat (group_card G hG') (mul m (group_card (subgroup_group G P) hP')) (st .snd .fst)
            = group_card G hG by fingp_group_card_irrel G hG' hG
            = mul c (suc. k) by hn ∎) in
    transport Nat (NatDivides (cardinality (SylowSubgroups p G) (sylow_subgroups_finite p hp G P sP))) m c mc (st .snd .snd)

def fingp_three_ne_one (e : Id Nat (suc. (suc. (suc. zero.))) (suc. zero.)) : Empty
  ≔ nat_encode (suc. (suc. (suc. zero.))) (suc. zero.) e

{` 2 ≢ 1 (mod 3). `}
def fingp_two_not_one_mod_three (h : NatCongruent (suc. (suc. (suc. zero.))) (suc. (suc. zero.)) (suc. zero.)) : Empty
  ≔ fingp_three_ne_one (nat_divides_one (suc. (suc. (suc. zero.)))
      (fingp_congruent_divides_diff (suc. (suc. (suc. zero.))) (suc. (suc. zero.)) (suc. zero.) (suc. zero.)
        (refl (suc. (suc. zero.) : Nat)) h))

{` The 3-cycle (0 1 2) of Fin 3. `}
def fin3_cycle : Fin three → Fin three ≔ [
  | inr. u ↦ inl. (inr. u)
  | inl. (inr. u) ↦ inl. (inl. (inr. u))
  | inl. (inl. (inr. u)) ↦ inr. u
  | inl. (inl. (inl. e)) ↦ match e [] ]

def fin3_cycle_cube : (x : Fin three) → Id (Fin three) (fin3_cycle (fin3_cycle (fin3_cycle x))) x
  ≔ decision_bool_reflect ((x : Fin three) → Id (Fin three) (fin3_cycle (fin3_cycle (fin3_cycle x))) x)
      (fin_forall_decidable three (x ↦ Id (Fin three) (fin3_cycle (fin3_cycle (fin3_cycle x))) x)
        (x ↦ fin_decidable_equality three (fin3_cycle (fin3_cycle (fin3_cycle x))) x))
      (refl (true. : Bool))

def sigma3_three_cycle : USym (symmetric_group three)
  ≔ permutation_symmetry (standard_set three) (perm3_equiv (Fin three) fin3_cycle fin3_cycle_cube)

def sigma3_three_cycle_cube
  : Id (USym (symmetric_group three)) (usym_power (symmetric_group three) sigma3_three_cycle (suc. (suc. (suc. zero.))))
      (usym_unit (symmetric_group three))
  ≔ perm3_symmetry_cube (standard_set three) fin3_cycle fin3_cycle_cube

def sigma3_three_cycle_ne : Not (Id (USym (symmetric_group three)) sigma3_three_cycle (usym_unit (symmetric_group three)))
  ≔ perm_symmetry_ne_unit (standard_set three) (perm3_equiv (Fin three) fin3_cycle fin3_cycle_cube) fin3_zero
      (nat_decision_false_reflect (Id (Fin three) (fin3_cycle fin3_zero) fin3_zero)
        (fin_decidable_equality three (fin3_cycle fin3_zero) fin3_zero) (refl (false. : Bool)))

{` H = ⟨(0 1 2)⟩, a subgroup with underlying group C_3. `}
def sigma3_sylow_three : Subgroups (symmetric_group three)
  ≔ cyclic_prime_subgroup (suc. (suc. zero.)) nat_prime_three (symmetric_group three) sigma3_three_cycle
      sigma3_three_cycle_cube sigma3_three_cycle_ne

def sigma3_largest_three
  : IsLargestPrimePower (suc. (suc. (suc. zero.))) (suc. zero.) (suc. (suc. (suc. (suc. (suc. (suc. zero.))))))
  ≔ fingp_largest_power_decide (suc. (suc. (suc. zero.))) (suc. zero.) (suc. (suc. (suc. (suc. (suc. (suc. zero.))))))
      (refl (true. : Bool)) (refl (false. : Bool))

def sigma3_sylow_three_is_sylow : IsSylowSubgroup (suc. (suc. (suc. zero.))) (symmetric_group three) sigma3_sylow_three
  ≔ cyclic_prime_sylow (suc. (suc. zero.)) nat_prime_three (symmetric_group three) (symmetric_group_finite three)
      sigma3_three_cycle sigma3_three_cycle_cube sigma3_three_cycle_ne
      (suc. (suc. (suc. (suc. (suc. (suc. zero.)))))) symmetric_group_three_card sigma3_largest_three

{` |Syl_3(Σ_3)| = 1. `}
def sigma3_sylow_three_count
  : Id Nat (cardinality (SylowSubgroups (suc. (suc. (suc. zero.))) (symmetric_group three))
      (sylow_subgroups_finite (suc. (suc. (suc. zero.))) nat_prime_three (symmetric_group three) sigma3_sylow_three
        sigma3_sylow_three_is_sylow))
      (suc. zero.)
  ≔ let p : Nat ≔ suc. (suc. (suc. zero.)) in
    let G ≔ symmetric_group three in
    let P ≔ sigma3_sylow_three in
    let sP ≔ sigma3_sylow_three_is_sylow in
    let d ≔ cardinality (SylowSubgroups p G) (sylow_subgroups_finite p nat_prime_three G P sP) in
    let hP ≔ cyclic_prime_subgroup_finite (suc. (suc. zero.)) nat_prime_three G sigma3_three_cycle sigma3_three_cycle_cube
      sigma3_three_cycle_ne in
    let dv : NatDivides d (suc. (suc. zero.))
      ≔ sylow_count_divides p nat_prime_three G P sP (symmetric_group_finite three) hP (suc. (suc. zero.)) (suc. (suc. zero.))
          symmetric_group_three_card
          (cyclic_prime_subgroup_card (suc. (suc. zero.)) nat_prime_three G sigma3_three_cycle sigma3_three_cycle_cube
            sigma3_three_cycle_ne hP) in
    let cong : NatCongruent p d (suc. zero.) ≔ sylow_three_congruence p nat_prime_three G P sP in
    match prime_divisors (suc. (suc. zero.)) nat_prime_two d dv [
    | inl. e ↦ e
    | inr. e2 ↦ absurd (Id Nat d (suc. zero.))
        (fingp_two_not_one_mod_three (transport Nat (x ↦ NatCongruent p x (suc. zero.)) d (suc. (suc. zero.)) e2 cong)) ]

{` Every subgroup of Σ_3 of order 3 is H; H is normal. `}
def sigma3_unique_order_three (T : Subgroups (symmetric_group three)) (hT : IsFiniteGroup (subgroup_group (symmetric_group three) T))
  (e : Id Nat (group_card (subgroup_group (symmetric_group three) T) hT) (suc. (suc. (suc. zero.))))
  : Id (Subgroups (symmetric_group three)) T sigma3_sylow_three
  ≔ sylow_card_one_unique (suc. (suc. (suc. zero.))) nat_prime_three (symmetric_group three) sigma3_sylow_three
      sigma3_sylow_three_is_sylow sigma3_sylow_three_count T
      (fingp_sylow_of_card (suc. (suc. (suc. zero.))) (symmetric_group three) (symmetric_group_finite three) T hT
        (suc. zero.) (suc. (suc. (suc. (suc. (suc. (suc. zero.)))))) symmetric_group_three_card e sigma3_largest_three)

def sigma3_sylow_three_normal : IsNormalSubgroup (symmetric_group three) sigma3_sylow_three
  ≔ sylow_card_one_normal (suc. (suc. (suc. zero.))) nat_prime_three (symmetric_group three) sigma3_sylow_three
      sigma3_sylow_three_is_sylow sigma3_sylow_three_count

{` The book's sentence in one statement: Σ_3 has a unique subgroup of order
   3, and it is normal. `}
def sigma3_unique_normal_order_three
  : Σ (Subgroups (symmetric_group three)) (S ↦ Product
      (Σ (IsFiniteGroup (subgroup_group (symmetric_group three) S))
        (h ↦ Id Nat (group_card (subgroup_group (symmetric_group three) S) h) (suc. (suc. (suc. zero.)))))
      (Product
        ((T : Subgroups (symmetric_group three)) (hT : IsFiniteGroup (subgroup_group (symmetric_group three) T))
          → Id Nat (group_card (subgroup_group (symmetric_group three) T) hT) (suc. (suc. (suc. zero.)))
          → Id (Subgroups (symmetric_group three)) T S)
        (IsNormalSubgroup (symmetric_group three) S)))
  ≔ let hP ≔ cyclic_prime_subgroup_finite (suc. (suc. zero.)) nat_prime_three (symmetric_group three) sigma3_three_cycle
      sigma3_three_cycle_cube sigma3_three_cycle_ne in
    (sigma3_sylow_three,
     ((hP, cyclic_prime_subgroup_card (suc. (suc. zero.)) nat_prime_three (symmetric_group three) sigma3_three_cycle
        sigma3_three_cycle_cube sigma3_three_cycle_ne hP),
      (sigma3_unique_order_three, sigma3_sylow_three_normal)))
