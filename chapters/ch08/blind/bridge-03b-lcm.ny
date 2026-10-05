export "03-pullback"
export "../../../src/890-integer-intersection-subgroups"

{` Bridges bridge for congp.tex:471 (aℤ ∩ bℤ = lcm(a,b)ℤ), from
   integer_intersection_subgroups (module 890, all a, b : ℕ, subgroup
   formulation). The blind aℤ is our multiples_subgroup (same cases, a
   different match, so identified pointwise); the blind intersection is our
   pullback group up to the proof that the pullback space is a groupoid (a
   proposition). The statement is written as a family over the choice of
   subgroups M : ℕ → Sub(ℤ) and that groupoid proof, and transported. `}

def b03_multiples_eq (C : CircleSignature) (a : Nat)
  : Id (Subgroups (circle_group C)) (multiples_subgroup C a) (blind_multiples_subgroup C a)
  ≔ match a [ zero. ↦ refl (rsub_subgroup C) | suc. k ↦ refl (rmsub_subgroup C k) ]

def b03_multiples_path (C : CircleSignature)
  : Id (Nat → Subgroups (circle_group C)) (multiples_subgroup C) (blind_multiples_subgroup C)
  ≔ funext Nat (_ ↦ Subgroups (circle_group C)) (multiples_subgroup C) (blind_multiples_subgroup C) (b03_multiples_eq C)

def B03PbSpace (C : CircleSignature) (M : Nat → Subgroups (circle_group C)) (a b : Nat) : Type
  ≔ let Z ≔ circle_group C in
    pbg_space Z (subgroup_to_mono Z (M a) .fst) (subgroup_to_mono Z (M b) .fst)
      (subgroup_to_mono Z (M a) .snd .fst) (subgroup_to_mono Z (M b) .snd .fst)

def B03Lcm (C : CircleSignature) (M : Nat → Subgroups (circle_group C)) (a b : Nat)
  (h : isGroupoid (B03PbSpace C M a b)) : Type
  ≔ let Z ≔ circle_group C in
    let ma ≔ subgroup_to_mono Z (M a) in let mb ≔ subgroup_to_mono Z (M b) in
    let mL ≔ subgroup_to_mono Z (M (nat_lcm a b)) in
    let P ≔ automorphism_group (B03PbSpace C M a b) h
              (pbg_point Z (ma .fst) (mb .fst) (ma .snd .fst) (mb .snd .fst)) in
    Σ (GroupIso P (mL .fst)) (phi ↦
      Id (GroupHom P Z)
        (group_hom_compose P (ma .fst) Z (mkhom P (ma .fst) (c ↦ c .fst .fst .fst, refl (shape (ma .fst)))) (ma .snd .fst))
        (group_hom_compose P (mL .fst) Z (phi .fst) (mL .snd .fst)))

def b03_blind_groupoid (C : CircleSignature) (M : Nat → Subgroups (circle_group C)) (a b : Nat)
  : isGroupoid (B03PbSpace C M a b)
  ≔ let Z ≔ circle_group C in
    blind_group_pullback_groupoid (subgroup_to_mono Z (M a) .fst) (subgroup_to_mono Z (M b) .fst) Z
      (subgroup_to_mono Z (M a) .snd .fst) (subgroup_to_mono Z (M b) .snd .fst)

def b03_our_groupoid (C : CircleSignature) (M : Nat → Subgroups (circle_group C)) (a b : Nat)
  : isGroupoid (B03PbSpace C M a b)
  ≔ let Z ≔ circle_group C in
    pbg_space_groupoid Z (subgroup_to_mono Z (M a) .fst) (subgroup_to_mono Z (M b) .fst)
      (subgroup_to_mono Z (M a) .snd .fst) (subgroup_to_mono Z (M b) .snd .fst)

{` congp.tex:471. `}
def bridge_ex_lcm_intersection : blind_ex_lcm_intersection
  ≔ C a b ↦
    let ours ≔ multiples_subgroup C in
    transport (Nat → Subgroups (circle_group C)) (M ↦ B03Lcm C M a b (b03_blind_groupoid C M a b))
      ours (blind_multiples_subgroup C) (b03_multiples_path C)
      (transport (isGroupoid (B03PbSpace C ours a b)) (h ↦ B03Lcm C ours a b h)
         (b03_our_groupoid C ours a b) (b03_blind_groupoid C ours a b)
         (isgroupoid_isprop (B03PbSpace C ours a b) (b03_our_groupoid C ours a b) (b03_blind_groupoid C ours a b))
         (integer_intersection_subgroups C a b))
