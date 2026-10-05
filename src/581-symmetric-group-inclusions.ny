export "507-subgroups-monos-equiv"
export "433-permutation-group-homomorphisms"

{` Chapter 5, ex:SGninSGn+1: i_n : Σ_n → Σ_{n+1} with Bi_n(A) = A ⊔ 1, pointed by
   reflexivity (judgmentally: (Fin n ⊔ 1, sum_set) is standard_set (n+1)),
   is a monomorphism; USym i_n extends a permutation of Fin n by fixing the
   last element. Bi_n is chapter 4's automorphism_group_map_hom for
   S ↦ S ⊔ 1 (module 431). `}

def set_plus_one (S : SetTypes) : SetTypes ≔ (Sum (S .fst) Unit, sum_set (S .fst) Unit (S .snd) unit_set)

def symmetric_group_inclusion (n : Nat) : GroupHom (symmetric_group n) (symmetric_group (suc. n))
  ≔ automorphism_group_map_hom SetTypes SetTypes sets_groupoid sets_groupoid set_plus_one (standard_set n)

def symmetric_group_inclusion_pointing (n : Nat)
  : Id (BG (symmetric_group (suc. n)) .carrier) (shape (symmetric_group (suc. n)))
      (hom_function (symmetric_group n) (symmetric_group (suc. n)) (symmetric_group_inclusion n) (shape (symmetric_group n)))
  ≔ refl (shape (symmetric_group (suc. n)))

{` Symmetries of permutation groups are determined by their actions. `}
def gset_permutation_ext (S : SetTypes) (p q : USym (permutation_group S))
  (h : (x : S .fst) → Id (S .fst) (permutation_action S p x) (permutation_action S q x))
  : Id (USym (permutation_group S)) p q
  ≔ let e ≔ compose_equiv (USym (permutation_group S)) (Id SetTypes S S) (Equiv (S .fst) (S .fst))
      (automorphism_group_usym_equiv SetTypes sets_groupoid S)
      (compose_equiv (Id SetTypes S S) (Id Type (S .fst) (S .fst)) (Equiv (S .fst) (S .fst))
        (subtype_path_equiv Type isSet isset_isprop S S) (transport_univalence_equiv (S .fst) (S .fst))) in
    equivalence_injective (USym (permutation_group S)) (Equiv (S .fst) (S .fst)) e p q
      (equiv_path (S .fst) (S .fst) (e .map p) (e .map q)
        (funext (S .fst) (_ ↦ S .fst) (permutation_action S p) (permutation_action S q) h))

{` USym i_n(π) acts as π on Fin n and fixes the new element. `}
def symmetric_group_inclusion_inl (n : Nat) (p : USym (symmetric_group n)) (x : Fin n)
  : Id (Fin (suc. n))
      (permutation_action (standard_set (suc. n))
        (usym_hom (symmetric_group n) (symmetric_group (suc. n)) (symmetric_group_inclusion n) p) (inl. x))
      (inl. (permutation_action (standard_set n) p x))
  ≔ let S ≔ standard_set n in
    let C ≔ Id SetTypes (set_plus_one S) (set_plus_one S) in
    concat (Fin (suc. n))
      (permutation_action (standard_set (suc. n))
        (usym_hom (symmetric_group n) (symmetric_group (suc. n)) (symmetric_group_inclusion n) p) (inl. x))
      (transport Type (Y ↦ Y) (Sum (Fin n) Unit) (Sum (Fin n) Unit) (refl ((Y ↦ Sum Y Unit) : Type → Type) (p .fst .fst)) (inl. x))
      (inl. (permutation_action S p x))
      (map_path C (Fin (suc. n)) (r ↦ transport Type (Y ↦ Y) (Sum (Fin n) Unit) (Sum (Fin n) Unit) (r .fst) (inl. x))
        (usym_hom (symmetric_group n) (symmetric_group (suc. n)) (symmetric_group_inclusion n) p .fst)
        (refl set_plus_one (p .fst))
        (automorphism_group_map_usym SetTypes SetTypes sets_groupoid sets_groupoid set_plus_one S p))
      (transport_sum_right_inl Unit (Fin n) (Fin n) (p .fst .fst) x)

def symmetric_group_inclusion_inr (n : Nat) (p : USym (symmetric_group n))
  : Id (Fin (suc. n))
      (permutation_action (standard_set (suc. n))
        (usym_hom (symmetric_group n) (symmetric_group (suc. n)) (symmetric_group_inclusion n) p) (inr. star.))
      (inr. star.)
  ≔ let S ≔ standard_set n in
    let C ≔ Id SetTypes (set_plus_one S) (set_plus_one S) in
    concat (Fin (suc. n))
      (permutation_action (standard_set (suc. n))
        (usym_hom (symmetric_group n) (symmetric_group (suc. n)) (symmetric_group_inclusion n) p) (inr. star.))
      (transport Type (Y ↦ Y) (Sum (Fin n) Unit) (Sum (Fin n) Unit) (refl ((Y ↦ Sum Y Unit) : Type → Type) (p .fst .fst)) (inr. star.))
      (inr. star.)
      (map_path C (Fin (suc. n)) (r ↦ transport Type (Y ↦ Y) (Sum (Fin n) Unit) (Sum (Fin n) Unit) (r .fst) (inr. star.))
        (usym_hom (symmetric_group n) (symmetric_group (suc. n)) (symmetric_group_inclusion n) p .fst)
        (refl set_plus_one (p .fst))
        (automorphism_group_map_usym SetTypes SetTypes sets_groupoid sets_groupoid set_plus_one S p))
      (transport_sum_right_inr Unit (Fin n) (Fin n) (p .fst .fst) star.)

def symmetric_group_inclusion_reflects (n : Nat)
  : PathReflecting (USym (symmetric_group n)) (USym (symmetric_group (suc. n)))
      (usym_hom (symmetric_group n) (symmetric_group (suc. n)) (symmetric_group_inclusion n))
  ≔ p q e ↦ gset_permutation_ext (standard_set n) p q
      (x ↦ inl_injective (Fin n) (permutation_action (standard_set n) p x) (permutation_action (standard_set n) q x)
        (calc
          (inl. (permutation_action (standard_set n) p x) : Fin (suc. n))
          = permutation_action (standard_set (suc. n))
              (usym_hom (symmetric_group n) (symmetric_group (suc. n)) (symmetric_group_inclusion n) p) (inl. x)
            by inverse (Fin (suc. n))
                 (permutation_action (standard_set (suc. n))
                   (usym_hom (symmetric_group n) (symmetric_group (suc. n)) (symmetric_group_inclusion n) p) (inl. x))
                 (inl. (permutation_action (standard_set n) p x)) (symmetric_group_inclusion_inl n p x)
          = permutation_action (standard_set (suc. n))
              (usym_hom (symmetric_group n) (symmetric_group (suc. n)) (symmetric_group_inclusion n) q) (inl. x)
            by map_path (USym (symmetric_group (suc. n))) (Fin (suc. n))
                 (r ↦ permutation_action (standard_set (suc. n)) r (inl. x))
                 (usym_hom (symmetric_group n) (symmetric_group (suc. n)) (symmetric_group_inclusion n) p)
                 (usym_hom (symmetric_group n) (symmetric_group (suc. n)) (symmetric_group_inclusion n) q) e
          = inl. (permutation_action (standard_set n) q x) by symmetric_group_inclusion_inl n q x ∎))

def symmetric_group_inclusion_mono (n : Nat)
  : IsGroupMono (symmetric_group n) (symmetric_group (suc. n)) (symmetric_group_inclusion n)
  ≔ path_reflecting_set_embedding (USym (symmetric_group n)) (USym (symmetric_group (suc. n)))
      (usym_set (symmetric_group (suc. n)))
      (usym_hom (symmetric_group n) (symmetric_group (suc. n)) (symmetric_group_inclusion n))
      (symmetric_group_inclusion_reflects n)

def symmetric_group_inclusion_monomorphism (n : Nat) : GroupMonos (symmetric_group (suc. n))
  ≔ (symmetric_group n, (symmetric_group_inclusion n, symmetric_group_inclusion_mono n))
