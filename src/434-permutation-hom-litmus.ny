export "433-permutation-group-homomorphisms"

{` Litmus checks for ex:groups-morphisms, item 1: Σ_2 → Σ_3 sends the
   transposition of Fin 2 to σ = (1 2) (the Fin 1 summand is 0 under
   fin_sum_equiv), and Σ_2 → Σ_4 sends it to the permutation (0 1)(2 3);
   the identification Fin(2·2) = Fin 2 × Fin 2 enumerates (a, b) as a + 2b. `}

def permhom_fin2_zero : Fin two ≔ inr. star.
def permhom_fin2_one : Fin two ≔ inl. (inr. star.)

def permhom_fin2_swap : Fin two → Fin two ≔ [
  | inr. u ↦ inl. (inr. u)
  | inl. (inr. u) ↦ inr. u
  | inl. (inl. e) ↦ match e [] ]

def permhom_fin2_swap_involutive (x : Fin two) : Id (Fin two) (permhom_fin2_swap (permhom_fin2_swap x)) x
  ≔ match x [
  | inr. u ↦ refl (inr. u : Fin two)
  | inl. (inr. u) ↦ refl (inl. (inr. u) : Fin two)
  | inl. (inl. e) ↦ match e [] ]

def permhom_fin2_swap_equiv : Equiv (Fin two) (Fin two)
  ≔ quasi_inverse_equiv (Fin two) (Fin two) permhom_fin2_swap permhom_fin2_swap
      permhom_fin2_swap_involutive permhom_fin2_swap_involutive

def permhom_sigma2_swap : USym (symmetric_group two)
  ≔ permutation_symmetry (standard_set two) permhom_fin2_swap_equiv

{` Two symmetries of Σ_S with the same action are equal
   (permutation_group_usym_equiv is an equivalence). `}
def permutation_symmetry_ext (S : SetTypes) (g h : USym (permutation_group S))
  (H : (x : S .fst) → Id (S .fst) (permutation_action S g x) (permutation_action S h x))
  : Id (USym (permutation_group S)) g h
  ≔ let X ≔ S .fst in
    let E ≔ permutation_group_usym_equiv S in
    equivalence_injective (USym (permutation_group S)) (Equiv X X) E g h
      (equiv_path X X (E .map g) (E .map h)
        (funext X (_ ↦ X) (E .map g .map) (E .map h .map)
          (x ↦ concat X (E .map g .map x) (permutation_action S g x) (E .map h .map x)
            (id_to_equiv_transport X X (g .fst .fst) x)
            (concat X (permutation_action S g x) (permutation_action S h x) (E .map h .map x)
              (H x)
              (inverse X (E .map h .map x) (permutation_action S h x) (id_to_equiv_transport X X (h .fst .fst) x))))))

{` Σ_2 → Σ_3 maps the transposition to σ = (1 2) of module 406. `}
def symmetric_sum_hom_swap_pointwise (x : Fin three)
  : Id (Fin three)
      (permutation_action (standard_set three)
        (usym_hom (symmetric_group two) (symmetric_group three) (symmetric_sum_hom two (suc. zero.)) permhom_sigma2_swap) x)
      (permutation_action (standard_set three) sigma3_sigma x)
  ≔ match x [
  | inr. u ↦ symmetric_sum_hom_fixes two (suc. zero.) permhom_sigma2_swap (inr. u)
  | inl. (inr. u) ↦ symmetric_sum_hom_acts two (suc. zero.) permhom_sigma2_swap (inr. u)
  | inl. (inl. (inr. u)) ↦ symmetric_sum_hom_acts two (suc. zero.) permhom_sigma2_swap (inl. (inr. u))
  | inl. (inl. (inl. e)) ↦ match e [] ]

def symmetric_sum_hom_swap_is_sigma
  : Id (USym (symmetric_group three))
      (usym_hom (symmetric_group two) (symmetric_group three) (symmetric_sum_hom two (suc. zero.)) permhom_sigma2_swap)
      sigma3_sigma
  ≔ permutation_symmetry_ext (standard_set three)
      (usym_hom (symmetric_group two) (symmetric_group three) (symmetric_sum_hom two (suc. zero.)) permhom_sigma2_swap)
      sigma3_sigma symmetric_sum_hom_swap_pointwise

{` The enumeration of Fin 2 × Fin 2: (1, 0) ↦ 1 and (0, 1) ↦ 2. `}
def permhom_four : Nat ≔ suc. (suc. (suc. (suc. zero.)))

def fin_product_enumeration_one_zero
  : Id (Fin permhom_four) (fin_product_equiv two two .map (permhom_fin2_one, permhom_fin2_zero)) (inl. (inr. star.))
  ≔ refl (inl. (inr. star.) : Fin permhom_four)

def fin_product_enumeration_zero_one
  : Id (Fin permhom_four) (fin_product_equiv two two .map (permhom_fin2_zero, permhom_fin2_one)) (inl. (inl. (inr. star.)))
  ≔ refl (inl. (inl. (inr. star.)) : Fin permhom_four)

{` Σ_2 → Σ_4 sends the transposition to (0 1)(2 3): 0 ↦ 1 and 2 ↦ 3. `}
def symmetric_product_hom_swap_zero
  : Id (Fin permhom_four)
      (permutation_action (standard_set permhom_four)
        (usym_hom (symmetric_group two) (symmetric_group permhom_four) (symmetric_product_hom two two) permhom_sigma2_swap)
        (inr. star.))
      (inl. (inr. star.))
  ≔ symmetric_product_hom_acts two two permhom_sigma2_swap permhom_fin2_zero permhom_fin2_zero

def symmetric_product_hom_swap_two
  : Id (Fin permhom_four)
      (permutation_action (standard_set permhom_four)
        (usym_hom (symmetric_group two) (symmetric_group permhom_four) (symmetric_product_hom two two) permhom_sigma2_swap)
        (inl. (inl. (inr. star.))))
      (inl. (inl. (inl. (inr. star.))))
  ≔ symmetric_product_hom_acts two two permhom_sigma2_swap permhom_fin2_zero permhom_fin2_one
