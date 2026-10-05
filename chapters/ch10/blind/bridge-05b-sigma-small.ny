export "05-examples"
export "bridge-04-sylow"
export "../../../src/1016-sigma-six-claims"
export "../../../src/1051-order-p-subgroup-count"
export "../../../src/941-image-consequences"

{` Bridges for the example at fingp.tex:27, first two paragraphs
   (Σ_3, Σ_4), 3^2 | n! for n > 5, and "for 2 < n ≤ 5 all subgroups of
   order 3 of Σ_n are conjugate" (they are 3-Sylow: 3 is the largest power
   of 3 dividing 3!, 4!, 5!). The blind subgroups of order k are our
   FiniteOrderSubgroups (module 1051) by refl. `}

def bridge_def_subgroups_of_order (G : Group) (k : Nat)
  : Id Type (BlindSubgroupsOfOrder G k) (FiniteOrderSubgroups G k) ≔ refl (FiniteOrderSubgroups G k)

{` Subgroups of order p^n, p^n the largest power of p dividing |G|, are the
   p-Sylow subgroups. `}
def bridge_sylow_order_data (p : Nat) (G : Group) (hG : IsFiniteGroup G) (n m : Nat) (hc : Id Nat (group_card G hG) m)
  (hl : IsLargestPrimePower p n m) (S : Subgroups G) (s : IsSylowSubgroup p G S)
  : Σ (IsFiniteGroup (subgroup_group G S)) (hS ↦ Id Nat (group_card (subgroup_group G S) hS) (nat_power p n))
  ≔ let hG' ≔ s .fst in
    let n' ≔ s .snd .snd .fst in
    let hl' : IsLargestPrimePower p n (group_card G hG')
      ≔ transport Nat (IsLargestPrimePower p n) m (group_card G hG')
          (inverse Nat (group_card G hG') m (concat Nat (group_card G hG') (group_card G hG) m (fingp_group_card_irrel G hG' hG) hc))
          hl in
    (s .snd .fst,
     concat Nat (group_card (subgroup_group G S) (s .snd .fst)) (nat_power p n') (nat_power p n)
       (s .snd .snd .snd .fst)
       (refl (nat_power p) (largest_prime_power_unique p (group_card G hG') n' n (s .snd .snd .snd .snd) hl')))

def bridge_order_sylow_equiv (p : Nat) (G : Group) (hG : IsFiniteGroup G) (n m : Nat) (hc : Id Nat (group_card G hG) m)
  (hl : IsLargestPrimePower p n m)
  : Equiv (FiniteOrderSubgroups G (nat_power p n)) (SylowSubgroups p G)
  ≔ family_equiv (Subgroups G)
      (S ↦ Σ (IsFiniteGroup (subgroup_group G S)) (hS ↦ Id Nat (group_card (subgroup_group G S) hS) (nat_power p n)))
      (IsSylowSubgroup p G)
      (S ↦ iff_equiv (Σ (IsFiniteGroup (subgroup_group G S)) (hS ↦ Id Nat (group_card (subgroup_group G S) hS) (nat_power p n)))
        (IsSylowSubgroup p G S) (finite_order_data_prop G (nat_power p n) S) (is_sylow_subgroup_prop p G S)
        (u ↦ fingp_sylow_of_card p G hG S (u .fst) n m hc (u .snd) hl)
        (bridge_sylow_order_data p G hG n m hc hl S))

{` Σ_3. `}
def bridge_sigma3_unique_order3 : blind_sigma3_unique_order3
  ≔ let G ≔ symmetric_group three in
    let c0 : FiniteOrderSubgroups G three
      ≔ (sigma3_sylow_three, bridge_sylow_order_data three G (symmetric_group_finite three) (suc. zero.) (factorial three)
           (symmetric_group_card three) sigma3_largest_three sigma3_sylow_three sigma3_sylow_three_is_sylow) in
    (c0, T ↦ finite_order_subgroups_path G three c0 T
       (inverse (Subgroups G) (T .fst) sigma3_sylow_three (sigma3_unique_order_three (T .fst) (T .snd .fst) (T .snd .snd))))

def bridge_sigma3_order3_normal : blind_sigma3_order3_normal
  ≔ S ↦ transport (Subgroups (symmetric_group three)) (IsNormalSubgroup (symmetric_group three)) sigma3_sylow_three (S .fst)
      (inverse (Subgroups (symmetric_group three)) (S .fst) sigma3_sylow_three
        (sigma3_unique_order_three (S .fst) (S .snd .fst) (S .snd .snd)))
      sigma3_sylow_three_normal

{` Σ_4: order-3 subgroups are the 3-Sylow subgroups. `}
def bridge_sigma4_order_sylow : Equiv (FiniteOrderSubgroups (symmetric_group 4) 3) (SylowSubgroups 3 (symmetric_group 4))
  ≔ bridge_order_sylow_equiv 3 (symmetric_group 4) (symmetric_group_finite 4) (suc. zero.) (factorial 4)
      (symmetric_group_card 4) sigma4_largest_three

def bridge_sigma4_order3_count : blind_sigma4_order3_count
  ≔ let A ≔ FiniteOrderSubgroups (symmetric_group 4) 3 in
    let Z ≔ SylowSubgroups 3 (symmetric_group 4) in
    let hZ ≔ sylow_subgroups_finite 3 nat_prime_three (symmetric_group 4) sigma4_sylow_p sigma4_sylow_p_is_sylow in
    let hA ≔ finite_of_equiv A Z bridge_sigma4_order_sylow hZ in
    (hA, concat Nat (cardinality A hA) (cardinality Z hZ) 4 (cardinality_equiv A Z bridge_sigma4_order_sylow hA hZ)
           sigma4_sylow_three_count)

def bridge_sigma4_order3_one_or_four : blind_sigma4_order3_one_or_four ≔ inr. bridge_sigma4_order3_count

def bridge_sigma4_order3_conjugate : blind_sigma4_order3_conjugate
  ≔ S T ↦ bridge_conjugate_from (symmetric_group 4) (S .fst) (T .fst)
      (sylow_subgroups_conjugate 3 nat_prime_three (symmetric_group 4) (S .fst) (T .fst)
        (bridge_sigma4_order_sylow .map S .snd) (bridge_sigma4_order_sylow .map T .snd))

{` The image in Σ_4 of the order-3 subgroup of Σ_3 has order 3 (the
   inclusion is a monomorphism), so if it were normal it would be the only
   3-Sylow subgroup, but ⟨(0 1 2)⟩ ≠ ⟨(1 2 3)⟩. `}
def bridge_symmetric_inclusion_mono (n : Nat)
  : IsGroupMonomorphism (symmetric_group n) (symmetric_group (suc. n)) (symmetric_group_inclusion n)
  ≔ equiv_inverse_map (IsGroupMonomorphism (symmetric_group n) (symmetric_group (suc. n)) (symmetric_group_inclusion n))
      (IsGroupMono (symmetric_group n) (symmetric_group (suc. n)) (symmetric_group_inclusion n))
      (group_monomorphism_mono_equiv (symmetric_group n) (symmetric_group (suc. n)) (symmetric_group_inclusion n))
      (path_reflecting_set_embedding (USym (symmetric_group n)) (USym (symmetric_group (suc. n)))
        (usym_set (symmetric_group (suc. n)))
        (usym_hom (symmetric_group n) (symmetric_group (suc. n)) (symmetric_group_inclusion n))
        (symmetric_group_inclusion_reflects n))

def bridge_image_order (G G' : Group) (S : Subgroups G) (f : GroupHom G G') (mf : IsGroupMonomorphism G G' f)
  : Id Group (subgroup_group G S) (subgroup_group G' (blind_subgroup_image G G' f S))
  ≔ let H ≔ subgroup_group G S in
    let k ≔ group_hom_compose H G G' (subgroup_inclusion G S) f in
    let mk : IsGroupMonomorphism H G' k
      ≔ group_monomorphism_compose H G G' (subgroup_inclusion G S) f
          (equiv_inverse_map (IsGroupMonomorphism H G (subgroup_inclusion G S)) (IsGroupMono H G (subgroup_inclusion G S))
            (group_monomorphism_mono_equiv H G (subgroup_inclusion G S)) (subgroup_inclusion_mono G S))
          mf in
    group_path_from_iso H (image_group H G' k) (image_projection H G' k, chim_mono_image_projection_iso H G' k mk)

def bridge_sigma4_image_not_normal : blind_sigma4_image_not_normal
  ≔ S n ↦
    let G3 ≔ symmetric_group 3 in let G ≔ symmetric_group 4 in
    let I ≔ blind_subgroup_image G3 G (symmetric_group_inclusion 3) (S .fst) in
    let pth ≔ bridge_image_order G3 G (S .fst) (symmetric_group_inclusion 3) (bridge_symmetric_inclusion_mono 3) in
    let hI ≔ group_finite_path (subgroup_group G3 (S .fst)) (subgroup_group G I) pth (S .snd .fst) in
    let cI : Id Nat (group_card (subgroup_group G I) hI) (nat_power 3 (suc. zero.))
      ≔ concat Nat (group_card (subgroup_group G I) hI) (group_card (subgroup_group G3 (S .fst)) (S .snd .fst)) 3
          (inverse Nat (group_card (subgroup_group G3 (S .fst)) (S .snd .fst)) (group_card (subgroup_group G I) hI)
            (group_card_path (subgroup_group G3 (S .fst)) (subgroup_group G I) pth (S .snd .fst) hI))
          (S .snd .snd) in
    let sI ≔ fingp_sylow_of_card 3 G (symmetric_group_finite 4) I hI (suc. zero.) (factorial 4) (symmetric_group_card 4) cI
      sigma4_largest_three in
    let fixed ≔ normal_iff_fixed G I .fst n in
    let to_I : (Q : Subgroups G) → IsSylowSubgroup 3 G Q → Id (Subgroups G) Q I
      ≔ Q sQ ↦ mere_rec (Σ (USym G) (g ↦ Id (Subgroups G) (subgroup_conjugate G g I) Q)) (Id (Subgroups G) Q I)
          (subgroups_set G Q I)
          (u ↦ concat (Subgroups G) Q (subgroup_conjugate G (u .fst) I) I
                 (inverse (Subgroups G) (subgroup_conjugate G (u .fst) I) Q (u .snd)) (fixed (u .fst)))
          (sylow_subgroups_conjugate 3 nat_prime_three G I Q sI sQ) in
    sigma4_sylow_p_ne_q
      (concat (Subgroups G) sigma4_sylow_p I sigma4_sylow_q (to_I sigma4_sylow_p sigma4_sylow_p_is_sylow)
        (inverse (Subgroups G) sigma4_sylow_q I (to_I sigma4_sylow_q sigma4_sylow_q_is_sylow)))

{` 3^2 | n! for n > 5. `}
def bridge_nine_divides_factorial : blind_nine_divides_factorial
  ≔ m ↦ transport Nat (k ↦ NatDivides 9 (factorial k)) (add sigma6_n m) (add m 6) (add_comm sigma6_n m)
      (factorial_nine_divides_shift m)

{` For n = 3, 4, 5 every subgroup of order 3 is 3-Sylow, hence they are all conjugate. `}
def bridge_sigma5_largest_three : IsLargestPrimePower 3 (suc. zero.) (factorial 5)
  ≔ fingp_largest_power_decide 3 (suc. zero.) (factorial 5) (refl (true. : Bool)) (refl (false. : Bool))

def bridge_small_order3_conjugate (n : Nat) (hl : IsLargestPrimePower 3 (suc. zero.) (factorial n))
  (S T : FiniteOrderSubgroups (symmetric_group n) 3)
  : BlindConjugate (symmetric_group n) (S .fst) (T .fst)
  ≔ let e ≔ bridge_order_sylow_equiv 3 (symmetric_group n) (symmetric_group_finite n) (suc. zero.) (factorial n)
        (symmetric_group_card n) hl in
    bridge_conjugate_from (symmetric_group n) (S .fst) (T .fst)
      (sylow_subgroups_conjugate 3 nat_prime_three (symmetric_group n) (S .fst) (T .fst) (e .map S .snd) (e .map T .snd))

def bridge_sigman_order3_conjugate_small : blind_sigman_order3_conjugate_small
  ≔ m hm ↦ match m [
  | zero. ↦ bridge_small_order3_conjugate 3 sigma3_largest_three
  | suc. zero. ↦ bridge_small_order3_conjugate 4 sigma4_largest_three
  | suc. (suc. zero.) ↦ bridge_small_order3_conjugate 5 bridge_sigma5_largest_three
  | suc. (suc. (suc. k)) ↦ match hm [] ]
