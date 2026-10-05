export "410-pointed-connected-groupoids"

{` The permutation group Σ_S acts on S; the symmetries in Σ_S are the
   permutations of S, via the map g ↦ (transport along g), whose underlying
   function is permutation_action of module 404 by definition. `}
def permutation_action_equiv (S : SetTypes) : Equiv (USym (permutation_group S)) (Equiv (S .fst) (S .fst))
  ≔ compose_equiv (USym (permutation_group S)) (Id Type (S .fst) (S .fst)) (Equiv (S .fst) (S .fst))
      (compose_equiv (USym (permutation_group S)) (Id SetTypes S S) (Id Type (S .fst) (S .fst))
        (automorphism_group_usym_equiv SetTypes sets_groupoid S)
        (subtype_path_equiv Type isSet isset_isprop S S))
      (transport_univalence_equiv (S .fst) (S .fst))

def permutation_action_equiv_map (S : SetTypes) (g : USym (permutation_group S)) (x : S .fst)
  : Id (S .fst) (permutation_action_equiv S .map g .map x) (permutation_action S g x)
  ≔ refl (permutation_action S g x)

{` Two symmetries of Σ_S are equal as soon as they act equally. `}
def permutation_symmetries_ext (S : SetTypes) (g h : USym (permutation_group S))
  (k : (x : S .fst) → Id (S .fst) (permutation_action S g x) (permutation_action S h x))
  : Id (USym (permutation_group S)) g h
  ≔ equivalence_injective (USym (permutation_group S)) (Equiv (S .fst) (S .fst)) (permutation_action_equiv S) g h
      (equiv_homotopy (S .fst) (S .fst) (permutation_action_equiv S .map g) (permutation_action_equiv S .map h) k)

{` ex:cyclicgroups, footnote: Σ_m has m! symmetries (factorial and
   fin_automorphisms_equiv of module 175). `}
def symmetric_group_finite (n : Nat) : IsFiniteGroup (symmetric_group n)
  ≔ mere (Σ Nat (k ↦ Id Type (USym (symmetric_group n)) (Fin k)))
      (factorial n, ua (USym (symmetric_group n)) (Fin (factorial n))
        (compose_equiv (USym (symmetric_group n)) (Equiv (Fin n) (Fin n)) (Fin (factorial n))
          (symmetric_group_usym_equiv n) (fin_automorphisms_equiv n)))

def symmetric_group_card (n : Nat)
  : Id Nat (group_card (symmetric_group n) (symmetric_group_finite n)) (factorial n)
  ≔ cardinality_from_path (USym (symmetric_group n)) (symmetric_group_finite n) (factorial n)
      (ua (USym (symmetric_group n)) (Fin (factorial n))
        (compose_equiv (USym (symmetric_group n)) (Equiv (Fin n) (Fin n)) (Fin (factorial n))
          (symmetric_group_usym_equiv n) (fin_automorphisms_equiv n)))

{` Litmus: Σ_3 has 6 symmetries. `}
def symmetric_group_three_card
  : Id Nat (group_card (symmetric_group (suc. two)) (symmetric_group_finite (suc. two)))
      (suc. (suc. (suc. (suc. (suc. (suc. zero.))))))
  ≔ symmetric_group_card (suc. two)

{` The symmetric group Σ_2. Fin 2 has 0 = inr star and 1 = inl (inr star). `}
def fin2_zero : Fin two ≔ inr. star.
def fin2_one : Fin two ≔ inl. (inr. star.)

def fin2_swap : Fin two → Fin two ≔ [
  | inr. u ↦ inl. (inr. u)
  | inl. (inr. u) ↦ inr. u
  | inl. (inl. e) ↦ match e [] ]

def fin2_swap_involutive (x : Fin two) : Id (Fin two) (fin2_swap (fin2_swap x)) x
  ≔ match x [
  | inr. u ↦ refl (inr. u : Fin two)
  | inl. (inr. u) ↦ refl (inl. (inr. u) : Fin two)
  | inl. (inl. e) ↦ match e [] ]

def fin2_swap_equiv : Equiv (Fin two) (Fin two)
  ≔ quasi_inverse_equiv (Fin two) (Fin two) fin2_swap fin2_swap fin2_swap_involutive fin2_swap_involutive

def fin2_code : Fin two → Type ≔ [ inr. _ ↦ Unit | inl. _ ↦ Empty ]

def fin2_zero_ne_one (p : Id (Fin two) fin2_zero fin2_one) : Empty
  ≔ transport (Fin two) fin2_code fin2_zero fin2_one p star.

def fin2_inr_path (u v : Unit) : Id (Fin two) (inr. u) (inr. v)
  ≔ refl ((w ↦ inr. w) : Unit → Fin two) (unit_prop u v)

def fin2_inl_path (u v : Unit) : Id (Fin two) (inl. (inr. u)) (inl. (inr. v))
  ≔ refl ((w ↦ inl. (inr. w)) : Unit → Fin two) (unit_prop u v)

{` Two different elements of Fin 2 are swapped. `}
def fin2_distinct_other (x y : Fin two) (h : Id (Fin two) x y → Empty) : Id (Fin two) y (fin2_swap x)
  ≔ match x, y [
  | inr. u, inr. v ↦ match h (fin2_inr_path u v) []
  | inr. u, inl. (inr. v) ↦ fin2_inl_path v u
  | inr. u, inl. (inl. e) ↦ match e []
  | inl. (inr. u), inr. v ↦ fin2_inr_path v u
  | inl. (inr. u), inl. (inr. v) ↦ match h (fin2_inl_path u v) []
  | inl. (inr. u), inl. (inl. e) ↦ match e []
  | inl. (inl. e), _ ↦ match e [] ]

{` The automorphisms of Fin 2 are determined by the image of 0. `}
def fin2_automorphism : Fin two → Equiv (Fin two) (Fin two) ≔ [
  | inr. _ ↦ identity_equiv (Fin two)
  | inl. (inr. _) ↦ fin2_swap_equiv
  | inl. (inl. e) ↦ match e [] ]

def fin2_automorphism_zero (b : Fin two) : Id (Fin two) (fin2_automorphism b .map fin2_zero) b
  ≔ match b [
  | inr. u ↦ fin2_inr_path star. u
  | inl. (inr. u) ↦ fin2_inl_path star. u
  | inl. (inl. e) ↦ match e [] ]

def fin2_automorphism_one (b : Fin two) : Id (Fin two) (fin2_automorphism b .map fin2_one) (fin2_swap b)
  ≔ match b [
  | inr. u ↦ fin2_inl_path star. u
  | inl. (inr. u) ↦ fin2_inr_path star. u
  | inl. (inl. e) ↦ match e [] ]

def fin2_equiv_other (e : Equiv (Fin two) (Fin two))
  : Id (Fin two) (e .map fin2_one) (fin2_swap (e .map fin2_zero))
  ≔ fin2_distinct_other (e .map fin2_zero) (e .map fin2_one)
      (p ↦ fin2_zero_ne_one (equivalence_injective (Fin two) (Fin two) e fin2_zero fin2_one p))

def fin2_automorphism_eta (e : Equiv (Fin two) (Fin two))
  : Id (Equiv (Fin two) (Fin two)) (fin2_automorphism (e .map fin2_zero)) e
  ≔ equiv_homotopy (Fin two) (Fin two) (fin2_automorphism (e .map fin2_zero)) e [
  | inr. u ↦ match u [ star. ↦ fin2_automorphism_zero (e .map fin2_zero) ]
  | inl. (inr. u) ↦ match u [ star. ↦
      concat (Fin two) (fin2_automorphism (e .map fin2_zero) .map fin2_one) (fin2_swap (e .map fin2_zero))
        (e .map fin2_one) (fin2_automorphism_one (e .map fin2_zero))
        (inverse (Fin two) (e .map fin2_one) (fin2_swap (e .map fin2_zero)) (fin2_equiv_other e)) ]
  | inl. (inl. v) ↦ match v [] ]

def fin2_automorphisms_equiv : Equiv (Equiv (Fin two) (Fin two)) (Fin two)
  ≔ quasi_inverse_equiv (Equiv (Fin two) (Fin two)) (Fin two) (e ↦ e .map fin2_zero) fin2_automorphism
      fin2_automorphism_eta fin2_automorphism_zero

{` USym Σ_2 ≃ Fin 2, by evaluating the action at 0. `}
def sigma2_usym_equiv : Equiv (USym (symmetric_group two)) (Fin two)
  ≔ compose_equiv (USym (symmetric_group two)) (Equiv (Fin two) (Fin two)) (Fin two)
      (permutation_action_equiv (standard_set two)) fin2_automorphisms_equiv

def sigma2_usym_equiv_map (g : USym (symmetric_group two))
  : Id (Fin two) (sigma2_usym_equiv .map g) (permutation_action (standard_set two) g fin2_zero)
  ≔ refl (permutation_action (standard_set two) g fin2_zero)

def sigma2_eval (g : USym (symmetric_group two)) : Fin two ≔ permutation_action (standard_set two) g fin2_zero

{` The swap symmetry of 2 in FinSet_2 (given by univalence from the swap). `}
def sigma2_swap : USym (symmetric_group two) ≔ permutation_symmetry (standard_set two) fin2_swap_equiv

def sigma2_swap_value : Id (Fin two) (sigma2_usym_equiv .map sigma2_swap) fin2_one ≔ refl fin2_one

def sigma2_unit_value : Id (Fin two) (sigma2_usym_equiv .map (usym_unit (symmetric_group two))) fin2_zero
  ≔ permutation_action_unit (standard_set two) fin2_zero

{` swap ≠ refl, and swap · swap = refl. `}
def sigma2_swap_nontrivial (p : Id (USym (symmetric_group two)) sigma2_swap (usym_unit (symmetric_group two)))
  : Empty
  ≔ fin2_zero_ne_one
      (concat (Fin two) fin2_zero (sigma2_usym_equiv .map (usym_unit (symmetric_group two))) fin2_one
        (inverse (Fin two) (sigma2_usym_equiv .map (usym_unit (symmetric_group two))) fin2_zero sigma2_unit_value)
        (refl sigma2_eval (inverse (USym (symmetric_group two)) sigma2_swap
          (usym_unit (symmetric_group two)) p)))

def sigma2_swap_squared
  : Id (USym (symmetric_group two)) (usym_mul (symmetric_group two) sigma2_swap sigma2_swap)
      (usym_unit (symmetric_group two))
  ≔ permutation_symmetries_ext (standard_set two)
      (usym_mul (symmetric_group two) sigma2_swap sigma2_swap) (usym_unit (symmetric_group two))
      (x ↦ concat (Fin two) (permutation_action (standard_set two) (usym_mul (symmetric_group two) sigma2_swap sigma2_swap) x)
        x (permutation_action (standard_set two) (usym_unit (symmetric_group two)) x)
        (concat (Fin two) (permutation_action (standard_set two) (usym_mul (symmetric_group two) sigma2_swap sigma2_swap) x)
          (fin2_swap (fin2_swap x)) x
          (permutation_action_mul (standard_set two) sigma2_swap sigma2_swap x) (fin2_swap_involutive x))
        (inverse (Fin two) (permutation_action (standard_set two) (usym_unit (symmetric_group two)) x) x
          (permutation_action_unit (standard_set two) x)))

{` Every symmetry in Σ_2 is refl or swap. `}
def sigma2_representative : Fin two → USym (symmetric_group two) ≔ [
  | inr. _ ↦ usym_unit (symmetric_group two)
  | inl. (inr. _) ↦ sigma2_swap
  | inl. (inl. e) ↦ match e [] ]

def sigma2_representative_value (b : Fin two)
  : Id (Fin two) (sigma2_usym_equiv .map (sigma2_representative b)) b
  ≔ match b [
  | inr. u ↦ concat (Fin two) (sigma2_usym_equiv .map (usym_unit (symmetric_group two))) fin2_zero (inr. u)
      sigma2_unit_value (fin2_inr_path star. u)
  | inl. (inr. u) ↦ fin2_inl_path star. u
  | inl. (inl. e) ↦ match e [] ]

def sigma2_classification (g : USym (symmetric_group two))
  : Id (USym (symmetric_group two)) g (sigma2_representative (sigma2_usym_equiv .map g))
  ≔ equivalence_injective (USym (symmetric_group two)) (Fin two) sigma2_usym_equiv g
      (sigma2_representative (sigma2_usym_equiv .map g))
      (inverse (Fin two) (sigma2_usym_equiv .map (sigma2_representative (sigma2_usym_equiv .map g)))
        (sigma2_usym_equiv .map g) (sigma2_representative_value (sigma2_usym_equiv .map g)))

def sigma2_representative_cases (b : Fin two)
  : Sum (Id (USym (symmetric_group two)) (sigma2_representative b) (usym_unit (symmetric_group two)))
      (Id (USym (symmetric_group two)) (sigma2_representative b) sigma2_swap)
  ≔ match b [
  | inr. _ ↦ inl. (refl (usym_unit (symmetric_group two)))
  | inl. (inr. _) ↦ inr. (refl sigma2_swap)
  | inl. (inl. e) ↦ match e [] ]

def sigma2_cases (g : USym (symmetric_group two))
  : Sum (Id (USym (symmetric_group two)) g (usym_unit (symmetric_group two)))
      (Id (USym (symmetric_group two)) g sigma2_swap)
  ≔ match sigma2_representative_cases (sigma2_usym_equiv .map g) [
  | inl. p ↦ inl. (concat (USym (symmetric_group two)) g (sigma2_representative (sigma2_usym_equiv .map g))
      (usym_unit (symmetric_group two)) (sigma2_classification g) p)
  | inr. p ↦ inr. (concat (USym (symmetric_group two)) g (sigma2_representative (sigma2_usym_equiv .map g))
      sigma2_swap (sigma2_classification g) p) ]

{` Σ_2 is finite with 2 symmetries (2! = 2). `}
def sigma2_finite : IsFiniteGroup (symmetric_group two)
  ≔ mere (Σ Nat (k ↦ Id Type (USym (symmetric_group two)) (Fin k)))
      (two, ua (USym (symmetric_group two)) (Fin two) sigma2_usym_equiv)

def sigma2_card : Id Nat (group_card (symmetric_group two) sigma2_finite) two
  ≔ cardinality_from_path (USym (symmetric_group two)) sigma2_finite two
      (ua (USym (symmetric_group two)) (Fin two) sigma2_usym_equiv)

{` exer:first examples, first part: Σ_2 is abelian. The automorphisms of
   Fin 2 (identity and swap) commute. `}
def fin2_automorphism_commute (a b x : Fin two)
  : Id (Fin two) (fin2_automorphism a .map (fin2_automorphism b .map x))
      (fin2_automorphism b .map (fin2_automorphism a .map x))
  ≔ match a, b [
  | inr. _, inr. _ ↦ refl x
  | inr. _, inl. (inr. _) ↦ refl (fin2_swap x)
  | inr. _, inl. (inl. e) ↦ match e []
  | inl. (inr. _), inr. _ ↦ refl (fin2_swap x)
  | inl. (inr. _), inl. (inr. _) ↦ refl (fin2_swap (fin2_swap x))
  | inl. (inr. _), inl. (inl. e) ↦ match e []
  | inl. (inl. e), _ ↦ match e [] ]

def fin2_equivs_commute (e d : Equiv (Fin two) (Fin two)) (x : Fin two)
  : Id (Fin two) (e .map (d .map x)) (d .map (e .map x))
  ≔ let E ≔ fin2_automorphism (e .map fin2_zero) in
    let D ≔ fin2_automorphism (d .map fin2_zero) in
    let F ≔ Equiv (Fin two) (Fin two) in
    let ap1 : F → F → Fin two ≔ u v ↦ u .map (v .map x) in
    let ap2 : F → F → Fin two ≔ u v ↦ v .map (u .map x) in
    calc
      e .map (d .map x) = E .map (D .map x)
        by refl ap1 (inverse F E e (fin2_automorphism_eta e)) (inverse F D d (fin2_automorphism_eta d))
      = D .map (E .map x) by fin2_automorphism_commute (e .map fin2_zero) (d .map fin2_zero) x
      = d .map (e .map x) by refl ap2 (fin2_automorphism_eta e) (fin2_automorphism_eta d) ∎

def sigma2_abelian : IsAbelian (symmetric_group two)
  ≔ g h ↦ permutation_symmetries_ext (standard_set two)
      (usym_mul (symmetric_group two) g h) (usym_mul (symmetric_group two) h g)
      (x ↦ let act ≔ permutation_action (standard_set two) in
        calc
          act (usym_mul (symmetric_group two) g h) x = act g (act h x)
            by permutation_action_mul (standard_set two) g h x
          = act h (act g x)
            by fin2_equivs_commute (permutation_action_equiv (standard_set two) .map g)
              (permutation_action_equiv (standard_set two) .map h) x
          = act (usym_mul (symmetric_group two) h g) x
            by inverse (Fin two) (act (usym_mul (symmetric_group two) h g) x) (act h (act g x))
              (permutation_action_mul (standard_set two) h g x) ∎)
