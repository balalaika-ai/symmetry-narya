export "474-standard-bicycles"

{` The infinite dihedral and the quaternion bicycles are normal
   (group.tex 2093–2094): explicit symmetries reach every element from a base
   point, and normal_bicycle_from_point_surjective (xca:normal-bicycle-equiv)
   applies. Litmus: USym D∞ ≃ Z ⊔ Z and USym Q₈ ≃ Fin 8, |Q₈| = 8. `}

def dihedral_add_pred_right (x y : Int) : Id Int (int_add x (int_pred y)) (int_pred (int_add x y))
  ≔ permutation_power_pred Int int_succ_equiv y x

def dihedral_neg_succ (n : Int) : Id Int (int_neg (int_succ n)) (int_pred (int_neg n))
  ≔ match n [
  | pos. zero. ↦ refl (neg. zero. : Int)
  | pos. (suc. m) ↦ refl (neg. (suc. m) : Int)
  | neg. zero. ↦ refl (pos. zero. : Int)
  | neg. (suc. m) ↦ refl (pos. (suc. m) : Int) ]

def dihedral_neg_pred (n : Int) : Id Int (int_neg (int_pred n)) (int_succ (int_neg n))
  ≔ match n [
  | pos. zero. ↦ refl (pos. (suc. zero.) : Int)
  | pos. (suc. zero.) ↦ refl (pos. zero. : Int)
  | pos. (suc. (suc. m)) ↦ refl (neg. m : Int)
  | neg. m ↦ refl (pos. (suc. (suc. m)) : Int) ]

def dihedral_sub_sub (k n : Int) : Id Int (int_sub k (int_sub k n)) n
  ≔ calc
      int_sub k (int_sub k n) = int_add k (int_sub n k) by refl (int_add k) (int_neg_sub k n)
      = int_add (int_sub n k) k by int_add_comm k (int_sub n k)
      = n by int_sub_add n k ∎

{` Translations σ⁺_k : inl n ↦ inl (k + n), inr n ↦ inr (k + n). `}
def dihedral_shift_map (k : Int) : Sum Int Int → Sum Int Int
  ≔ [ inl. n ↦ inl. (int_add k n) | inr. n ↦ inr. (int_add k n) ]

def dihedral_shift_inverse_map (k : Int) : Sum Int Int → Sum Int Int
  ≔ [ inl. n ↦ inl. (int_add (int_neg k) n) | inr. n ↦ inr. (int_add (int_neg k) n) ]

def dihedral_shift_equiv (k : Int) : Equiv (Sum Int Int) (Sum Int Int)
  ≔ quasi_inverse_equiv (Sum Int Int) (Sum Int Int) (dihedral_shift_map k) (dihedral_shift_inverse_map k)
      [ inl. n ↦ inl. (int_translate_inverse k n) | inr. n ↦ inr. (int_translate_inverse k n) ]
      [ inl. n ↦ inl. (int_translate_inverse_other k n) | inr. n ↦ inr. (int_translate_inverse_other k n) ]

def dihedral_shift_iso (k : Int) : BicycleIsomorphisms infinite_dihedral_bicycle infinite_dihedral_bicycle
  ≔ (dihedral_shift_equiv k,
      ([ inl. n ↦ inl. (int_add_successor_right k n) | inr. n ↦ inr. (dihedral_add_pred_right k n) ],
       [ inl. n ↦ refl (inr. (int_add k n) : Sum Int Int) | inr. n ↦ refl (inl. (int_add k n) : Sum Int Int) ]))

{` Reflections σ⁻_k : inl n ↦ inr (k − n), inr n ↦ inl (k − n). `}
def dihedral_reflection_map (k : Int) : Sum Int Int → Sum Int Int
  ≔ [ inl. n ↦ inr. (int_sub k n) | inr. n ↦ inl. (int_sub k n) ]

def dihedral_reflection_involutive (k : Int) (x : Sum Int Int)
  : Id (Sum Int Int) (dihedral_reflection_map k (dihedral_reflection_map k x)) x
  ≔ match x [ inl. n ↦ inl. (dihedral_sub_sub k n) | inr. n ↦ inr. (dihedral_sub_sub k n) ]

def dihedral_reflection_equiv (k : Int) : Equiv (Sum Int Int) (Sum Int Int)
  ≔ quasi_inverse_equiv (Sum Int Int) (Sum Int Int) (dihedral_reflection_map k) (dihedral_reflection_map k)
      (dihedral_reflection_involutive k) (dihedral_reflection_involutive k)

def dihedral_reflection_iso (k : Int) : BicycleIsomorphisms infinite_dihedral_bicycle infinite_dihedral_bicycle
  ≔ (dihedral_reflection_equiv k,
      ([ inl. n ↦ inr. (concat Int (int_add k (int_neg (int_succ n))) (int_add k (int_pred (int_neg n)))
                    (int_pred (int_add k (int_neg n)))
                    (refl (int_add k) (dihedral_neg_succ n)) (dihedral_add_pred_right k (int_neg n)))
       | inr. n ↦ inl. (concat Int (int_add k (int_neg (int_pred n))) (int_add k (int_succ (int_neg n)))
                    (int_succ (int_add k (int_neg n)))
                    (refl (int_add k) (dihedral_neg_pred n)) (int_add_successor_right k (int_neg n))) ],
       [ inl. n ↦ refl (inl. (int_sub k n) : Sum Int Int) | inr. n ↦ refl (inr. (int_sub k n) : Sum Int Int) ]))

def dihedral_symmetry_from_origin (z : Sum Int Int)
  : BookFiber (Id Bicycles infinite_dihedral_bicycle infinite_dihedral_bicycle) (Sum Int Int)
      (bicycle_evaluation infinite_dihedral_bicycle (inl. int_zero)) z
  ≔ match z [
  | inl. k ↦ (bicycle_path_from_iso infinite_dihedral_bicycle infinite_dihedral_bicycle (dihedral_shift_iso k),
      refl (inl. k : Sum Int Int))
  | inr. k ↦ (bicycle_path_from_iso infinite_dihedral_bicycle infinite_dihedral_bicycle (dihedral_reflection_iso k),
      refl (inr. k : Sum Int Int)) ]

{` group.tex 2093: the infinite dihedral bicycle is normal. `}
def infinite_dihedral_bicycle_normal : IsNormalBicycle infinite_dihedral_bicycle
  ≔ normal_bicycle_from_point_surjective infinite_dihedral_bicycle (inl. int_zero)
      (z ↦ mere (BookFiber (Id Bicycles infinite_dihedral_bicycle infinite_dihedral_bicycle) (Sum Int Int)
          (bicycle_evaluation infinite_dihedral_bicycle (inl. int_zero)) z)
        (dihedral_symmetry_from_origin z))

{` Litmus: the symmetries of D∞ are Z ⊔ Z (evaluation at inl 0); the
   symmetry of inl k acts as the translation by k. `}
def infinite_dihedral_usym_equiv : Equiv (USym infinite_dihedral_group) (Sum Int Int)
  ≔ compose_equiv (USym infinite_dihedral_group) (Id Bicycles infinite_dihedral_bicycle infinite_dihedral_bicycle)
      (Sum Int Int)
      (automorphism_group_usym_equiv Bicycles bicycles_groupoid infinite_dihedral_bicycle)
      (native_equivalence (Id Bicycles infinite_dihedral_bicycle infinite_dihedral_bicycle) (Sum Int Int)
        (bicycle_evaluation_equiv infinite_dihedral_bicycle infinite_dihedral_bicycle_normal (inl. int_zero)))

def dihedral_shift_symmetry_acts (k n : Int)
  : Id (Sum Int Int)
      (bicycle_path_evaluate infinite_dihedral_bicycle infinite_dihedral_bicycle
        (bicycle_path_from_iso infinite_dihedral_bicycle infinite_dihedral_bicycle (dihedral_shift_iso k)) (inr. n))
      (inr. (int_add k n))
  ≔ refl (inr. (int_add k n) : Sum Int Int)

{` The eight symmetries of the quaternion bicycle (computed: exactly the
   permutations commuting with a and b), one for each image of 0. `}
{` The symmetry sending 0 to 0. `}
def quaternion_symmetry_0_map : Fin eight → Fin eight ≔ [
  | inr. u ↦ inr. u
  | inl. (inr. u) ↦ inl. (inr. u)
  | inl. (inl. (inr. u)) ↦ inl. (inl. (inr. u))
  | inl. (inl. (inl. (inr. u))) ↦ inl. (inl. (inl. (inr. u)))
  | inl. (inl. (inl. (inl. (inr. u)))) ↦ inl. (inl. (inl. (inl. (inr. u))))
  | inl. (inl. (inl. (inl. (inl. (inr. u))))) ↦ inl. (inl. (inl. (inl. (inl. (inr. u)))))
  | inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))) ↦ inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))) ↦ inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))))
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. e))))))) ↦ match e [] ]

def quaternion_symmetry_0_inverse_map : Fin eight → Fin eight ≔ [
  | inr. u ↦ inr. u
  | inl. (inr. u) ↦ inl. (inr. u)
  | inl. (inl. (inr. u)) ↦ inl. (inl. (inr. u))
  | inl. (inl. (inl. (inr. u))) ↦ inl. (inl. (inl. (inr. u)))
  | inl. (inl. (inl. (inl. (inr. u)))) ↦ inl. (inl. (inl. (inl. (inr. u))))
  | inl. (inl. (inl. (inl. (inl. (inr. u))))) ↦ inl. (inl. (inl. (inl. (inl. (inr. u)))))
  | inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))) ↦ inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))) ↦ inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))))
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. e))))))) ↦ match e [] ]

def quaternion_symmetry_0_equiv_retraction (x : Fin eight)
  : Id (Fin eight) (quaternion_symmetry_0_inverse_map (quaternion_symmetry_0_map x)) x
  ≔ match x [
  | inr. u ↦ refl (inr. u : Fin eight)
  | inl. (inr. u) ↦ refl (inl. (inr. u) : Fin eight)
  | inl. (inl. (inr. u)) ↦ refl (inl. (inl. (inr. u)) : Fin eight)
  | inl. (inl. (inl. (inr. u))) ↦ refl (inl. (inl. (inl. (inr. u))) : Fin eight)
  | inl. (inl. (inl. (inl. (inr. u)))) ↦ refl (inl. (inl. (inl. (inl. (inr. u)))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inr. u))))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inr. u))))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. e))))))) ↦ match e [] ]

def quaternion_symmetry_0_equiv_section (x : Fin eight)
  : Id (Fin eight) (quaternion_symmetry_0_map (quaternion_symmetry_0_inverse_map x)) x
  ≔ match x [
  | inr. u ↦ refl (inr. u : Fin eight)
  | inl. (inr. u) ↦ refl (inl. (inr. u) : Fin eight)
  | inl. (inl. (inr. u)) ↦ refl (inl. (inl. (inr. u)) : Fin eight)
  | inl. (inl. (inl. (inr. u))) ↦ refl (inl. (inl. (inl. (inr. u))) : Fin eight)
  | inl. (inl. (inl. (inl. (inr. u)))) ↦ refl (inl. (inl. (inl. (inl. (inr. u)))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inr. u))))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inr. u))))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. e))))))) ↦ match e [] ]

def quaternion_symmetry_0_equiv : Equiv (Fin eight) (Fin eight)
  ≔ quasi_inverse_equiv (Fin eight) (Fin eight) quaternion_symmetry_0_map quaternion_symmetry_0_inverse_map quaternion_symmetry_0_equiv_retraction quaternion_symmetry_0_equiv_section

def quaternion_symmetry_0_commutes_a (x : Fin eight)
  : Id (Fin eight) (quaternion_symmetry_0_map (quaternion_a_map x)) (quaternion_a_map (quaternion_symmetry_0_map x))
  ≔ match x [
  | inr. u ↦ refl (inl. (inr. u) : Fin eight)
  | inl. (inr. u) ↦ refl (inl. (inl. (inl. (inl. (inr. u)))) : Fin eight)
  | inl. (inl. (inr. u)) ↦ refl (inl. (inl. (inl. (inr. u))) : Fin eight)
  | inl. (inl. (inl. (inr. u))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))) : Fin eight)
  | inl. (inl. (inl. (inl. (inr. u)))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inr. u))))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inr. u))))) ↦ refl (inr. u : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))) ↦ refl (inl. (inl. (inr. u)) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. e))))))) ↦ match e [] ]

def quaternion_symmetry_0_commutes_b (x : Fin eight)
  : Id (Fin eight) (quaternion_symmetry_0_map (quaternion_b_map x)) (quaternion_b_map (quaternion_symmetry_0_map x))
  ≔ match x [
  | inr. u ↦ refl (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))) : Fin eight)
  | inl. (inr. u) ↦ refl (inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))) : Fin eight)
  | inl. (inl. (inr. u)) ↦ refl (inl. (inr. u) : Fin eight)
  | inl. (inl. (inl. (inr. u))) ↦ refl (inr. u : Fin eight)
  | inl. (inl. (inl. (inl. (inr. u)))) ↦ refl (inl. (inl. (inl. (inr. u))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inr. u))))) ↦ refl (inl. (inl. (inr. u)) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inr. u))))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))) ↦ refl (inl. (inl. (inl. (inl. (inr. u)))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. e))))))) ↦ match e [] ]

def quaternion_symmetry_0 : BicycleIsomorphisms quaternion_bicycle quaternion_bicycle
  ≔ (quaternion_symmetry_0_equiv, (quaternion_symmetry_0_commutes_a, quaternion_symmetry_0_commutes_b))

{` The symmetry sending 0 to 1. `}
def quaternion_symmetry_1_map : Fin eight → Fin eight ≔ [
  | inr. u ↦ inl. (inr. u)
  | inl. (inr. u) ↦ inl. (inl. (inl. (inl. (inr. u))))
  | inl. (inl. (inr. u)) ↦ inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))))
  | inl. (inl. (inl. (inr. u))) ↦ inl. (inl. (inr. u))
  | inl. (inl. (inl. (inl. (inr. u)))) ↦ inl. (inl. (inl. (inl. (inl. (inr. u)))))
  | inl. (inl. (inl. (inl. (inl. (inr. u))))) ↦ inr. u
  | inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))) ↦ inl. (inl. (inl. (inr. u)))
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))) ↦ inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. e))))))) ↦ match e [] ]

def quaternion_symmetry_1_inverse_map : Fin eight → Fin eight ≔ [
  | inr. u ↦ inl. (inl. (inl. (inl. (inl. (inr. u)))))
  | inl. (inr. u) ↦ inr. u
  | inl. (inl. (inr. u)) ↦ inl. (inl. (inl. (inr. u)))
  | inl. (inl. (inl. (inr. u))) ↦ inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))
  | inl. (inl. (inl. (inl. (inr. u)))) ↦ inl. (inr. u)
  | inl. (inl. (inl. (inl. (inl. (inr. u))))) ↦ inl. (inl. (inl. (inl. (inr. u))))
  | inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))) ↦ inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))))
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))) ↦ inl. (inl. (inr. u))
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. e))))))) ↦ match e [] ]

def quaternion_symmetry_1_equiv_retraction (x : Fin eight)
  : Id (Fin eight) (quaternion_symmetry_1_inverse_map (quaternion_symmetry_1_map x)) x
  ≔ match x [
  | inr. u ↦ refl (inr. u : Fin eight)
  | inl. (inr. u) ↦ refl (inl. (inr. u) : Fin eight)
  | inl. (inl. (inr. u)) ↦ refl (inl. (inl. (inr. u)) : Fin eight)
  | inl. (inl. (inl. (inr. u))) ↦ refl (inl. (inl. (inl. (inr. u))) : Fin eight)
  | inl. (inl. (inl. (inl. (inr. u)))) ↦ refl (inl. (inl. (inl. (inl. (inr. u)))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inr. u))))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inr. u))))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. e))))))) ↦ match e [] ]

def quaternion_symmetry_1_equiv_section (x : Fin eight)
  : Id (Fin eight) (quaternion_symmetry_1_map (quaternion_symmetry_1_inverse_map x)) x
  ≔ match x [
  | inr. u ↦ refl (inr. u : Fin eight)
  | inl. (inr. u) ↦ refl (inl. (inr. u) : Fin eight)
  | inl. (inl. (inr. u)) ↦ refl (inl. (inl. (inr. u)) : Fin eight)
  | inl. (inl. (inl. (inr. u))) ↦ refl (inl. (inl. (inl. (inr. u))) : Fin eight)
  | inl. (inl. (inl. (inl. (inr. u)))) ↦ refl (inl. (inl. (inl. (inl. (inr. u)))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inr. u))))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inr. u))))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. e))))))) ↦ match e [] ]

def quaternion_symmetry_1_equiv : Equiv (Fin eight) (Fin eight)
  ≔ quasi_inverse_equiv (Fin eight) (Fin eight) quaternion_symmetry_1_map quaternion_symmetry_1_inverse_map quaternion_symmetry_1_equiv_retraction quaternion_symmetry_1_equiv_section

def quaternion_symmetry_1_commutes_a (x : Fin eight)
  : Id (Fin eight) (quaternion_symmetry_1_map (quaternion_a_map x)) (quaternion_a_map (quaternion_symmetry_1_map x))
  ≔ match x [
  | inr. u ↦ refl (inl. (inl. (inl. (inl. (inr. u)))) : Fin eight)
  | inl. (inr. u) ↦ refl (inl. (inl. (inl. (inl. (inl. (inr. u))))) : Fin eight)
  | inl. (inl. (inr. u)) ↦ refl (inl. (inl. (inr. u)) : Fin eight)
  | inl. (inl. (inl. (inr. u))) ↦ refl (inl. (inl. (inl. (inr. u))) : Fin eight)
  | inl. (inl. (inl. (inl. (inr. u)))) ↦ refl (inr. u : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inr. u))))) ↦ refl (inl. (inr. u) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. e))))))) ↦ match e [] ]

def quaternion_symmetry_1_commutes_b (x : Fin eight)
  : Id (Fin eight) (quaternion_symmetry_1_map (quaternion_b_map x)) (quaternion_b_map (quaternion_symmetry_1_map x))
  ≔ match x [
  | inr. u ↦ refl (inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))) : Fin eight)
  | inl. (inr. u) ↦ refl (inl. (inl. (inl. (inr. u))) : Fin eight)
  | inl. (inl. (inr. u)) ↦ refl (inl. (inl. (inl. (inl. (inr. u)))) : Fin eight)
  | inl. (inl. (inl. (inr. u))) ↦ refl (inl. (inr. u) : Fin eight)
  | inl. (inl. (inl. (inl. (inr. u)))) ↦ refl (inl. (inl. (inr. u)) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inr. u))))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))) ↦ refl (inr. u : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inr. u))))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. e))))))) ↦ match e [] ]

def quaternion_symmetry_1 : BicycleIsomorphisms quaternion_bicycle quaternion_bicycle
  ≔ (quaternion_symmetry_1_equiv, (quaternion_symmetry_1_commutes_a, quaternion_symmetry_1_commutes_b))

{` The symmetry sending 0 to 2. `}
def quaternion_symmetry_2_map : Fin eight → Fin eight ≔ [
  | inr. u ↦ inl. (inl. (inr. u))
  | inl. (inr. u) ↦ inl. (inl. (inl. (inr. u)))
  | inl. (inl. (inr. u)) ↦ inl. (inl. (inl. (inl. (inr. u))))
  | inl. (inl. (inl. (inr. u))) ↦ inl. (inl. (inl. (inl. (inl. (inr. u)))))
  | inl. (inl. (inl. (inl. (inr. u)))) ↦ inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))
  | inl. (inl. (inl. (inl. (inl. (inr. u))))) ↦ inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))))
  | inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))) ↦ inr. u
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))) ↦ inl. (inr. u)
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. e))))))) ↦ match e [] ]

def quaternion_symmetry_2_inverse_map : Fin eight → Fin eight ≔ [
  | inr. u ↦ inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))
  | inl. (inr. u) ↦ inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))))
  | inl. (inl. (inr. u)) ↦ inr. u
  | inl. (inl. (inl. (inr. u))) ↦ inl. (inr. u)
  | inl. (inl. (inl. (inl. (inr. u)))) ↦ inl. (inl. (inr. u))
  | inl. (inl. (inl. (inl. (inl. (inr. u))))) ↦ inl. (inl. (inl. (inr. u)))
  | inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))) ↦ inl. (inl. (inl. (inl. (inr. u))))
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))) ↦ inl. (inl. (inl. (inl. (inl. (inr. u)))))
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. e))))))) ↦ match e [] ]

def quaternion_symmetry_2_equiv_retraction (x : Fin eight)
  : Id (Fin eight) (quaternion_symmetry_2_inverse_map (quaternion_symmetry_2_map x)) x
  ≔ match x [
  | inr. u ↦ refl (inr. u : Fin eight)
  | inl. (inr. u) ↦ refl (inl. (inr. u) : Fin eight)
  | inl. (inl. (inr. u)) ↦ refl (inl. (inl. (inr. u)) : Fin eight)
  | inl. (inl. (inl. (inr. u))) ↦ refl (inl. (inl. (inl. (inr. u))) : Fin eight)
  | inl. (inl. (inl. (inl. (inr. u)))) ↦ refl (inl. (inl. (inl. (inl. (inr. u)))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inr. u))))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inr. u))))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. e))))))) ↦ match e [] ]

def quaternion_symmetry_2_equiv_section (x : Fin eight)
  : Id (Fin eight) (quaternion_symmetry_2_map (quaternion_symmetry_2_inverse_map x)) x
  ≔ match x [
  | inr. u ↦ refl (inr. u : Fin eight)
  | inl. (inr. u) ↦ refl (inl. (inr. u) : Fin eight)
  | inl. (inl. (inr. u)) ↦ refl (inl. (inl. (inr. u)) : Fin eight)
  | inl. (inl. (inl. (inr. u))) ↦ refl (inl. (inl. (inl. (inr. u))) : Fin eight)
  | inl. (inl. (inl. (inl. (inr. u)))) ↦ refl (inl. (inl. (inl. (inl. (inr. u)))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inr. u))))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inr. u))))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. e))))))) ↦ match e [] ]

def quaternion_symmetry_2_equiv : Equiv (Fin eight) (Fin eight)
  ≔ quasi_inverse_equiv (Fin eight) (Fin eight) quaternion_symmetry_2_map quaternion_symmetry_2_inverse_map quaternion_symmetry_2_equiv_retraction quaternion_symmetry_2_equiv_section

def quaternion_symmetry_2_commutes_a (x : Fin eight)
  : Id (Fin eight) (quaternion_symmetry_2_map (quaternion_a_map x)) (quaternion_a_map (quaternion_symmetry_2_map x))
  ≔ match x [
  | inr. u ↦ refl (inl. (inl. (inl. (inr. u))) : Fin eight)
  | inl. (inr. u) ↦ refl (inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))) : Fin eight)
  | inl. (inl. (inr. u)) ↦ refl (inl. (inl. (inl. (inl. (inl. (inr. u))))) : Fin eight)
  | inl. (inl. (inl. (inr. u))) ↦ refl (inr. u : Fin eight)
  | inl. (inl. (inl. (inl. (inr. u)))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inr. u))))) ↦ refl (inl. (inl. (inr. u)) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))) ↦ refl (inl. (inr. u) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))) ↦ refl (inl. (inl. (inl. (inl. (inr. u)))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. e))))))) ↦ match e [] ]

def quaternion_symmetry_2_commutes_b (x : Fin eight)
  : Id (Fin eight) (quaternion_symmetry_2_map (quaternion_b_map x)) (quaternion_b_map (quaternion_symmetry_2_map x))
  ≔ match x [
  | inr. u ↦ refl (inl. (inr. u) : Fin eight)
  | inl. (inr. u) ↦ refl (inr. u : Fin eight)
  | inl. (inl. (inr. u)) ↦ refl (inl. (inl. (inl. (inr. u))) : Fin eight)
  | inl. (inl. (inl. (inr. u))) ↦ refl (inl. (inl. (inr. u)) : Fin eight)
  | inl. (inl. (inl. (inl. (inr. u)))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inr. u))))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inr. u))))) ↦ refl (inl. (inl. (inl. (inl. (inr. u)))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. e))))))) ↦ match e [] ]

def quaternion_symmetry_2 : BicycleIsomorphisms quaternion_bicycle quaternion_bicycle
  ≔ (quaternion_symmetry_2_equiv, (quaternion_symmetry_2_commutes_a, quaternion_symmetry_2_commutes_b))

{` The symmetry sending 0 to 3. `}
def quaternion_symmetry_3_map : Fin eight → Fin eight ≔ [
  | inr. u ↦ inl. (inl. (inl. (inr. u)))
  | inl. (inr. u) ↦ inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))
  | inl. (inl. (inr. u)) ↦ inl. (inr. u)
  | inl. (inl. (inl. (inr. u))) ↦ inl. (inl. (inl. (inl. (inr. u))))
  | inl. (inl. (inl. (inl. (inr. u)))) ↦ inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))))
  | inl. (inl. (inl. (inl. (inl. (inr. u))))) ↦ inl. (inl. (inr. u))
  | inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))) ↦ inl. (inl. (inl. (inl. (inl. (inr. u)))))
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))) ↦ inr. u
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. e))))))) ↦ match e [] ]

def quaternion_symmetry_3_inverse_map : Fin eight → Fin eight ≔ [
  | inr. u ↦ inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))))
  | inl. (inr. u) ↦ inl. (inl. (inr. u))
  | inl. (inl. (inr. u)) ↦ inl. (inl. (inl. (inl. (inl. (inr. u)))))
  | inl. (inl. (inl. (inr. u))) ↦ inr. u
  | inl. (inl. (inl. (inl. (inr. u)))) ↦ inl. (inl. (inl. (inr. u)))
  | inl. (inl. (inl. (inl. (inl. (inr. u))))) ↦ inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))
  | inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))) ↦ inl. (inr. u)
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))) ↦ inl. (inl. (inl. (inl. (inr. u))))
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. e))))))) ↦ match e [] ]

def quaternion_symmetry_3_equiv_retraction (x : Fin eight)
  : Id (Fin eight) (quaternion_symmetry_3_inverse_map (quaternion_symmetry_3_map x)) x
  ≔ match x [
  | inr. u ↦ refl (inr. u : Fin eight)
  | inl. (inr. u) ↦ refl (inl. (inr. u) : Fin eight)
  | inl. (inl. (inr. u)) ↦ refl (inl. (inl. (inr. u)) : Fin eight)
  | inl. (inl. (inl. (inr. u))) ↦ refl (inl. (inl. (inl. (inr. u))) : Fin eight)
  | inl. (inl. (inl. (inl. (inr. u)))) ↦ refl (inl. (inl. (inl. (inl. (inr. u)))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inr. u))))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inr. u))))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. e))))))) ↦ match e [] ]

def quaternion_symmetry_3_equiv_section (x : Fin eight)
  : Id (Fin eight) (quaternion_symmetry_3_map (quaternion_symmetry_3_inverse_map x)) x
  ≔ match x [
  | inr. u ↦ refl (inr. u : Fin eight)
  | inl. (inr. u) ↦ refl (inl. (inr. u) : Fin eight)
  | inl. (inl. (inr. u)) ↦ refl (inl. (inl. (inr. u)) : Fin eight)
  | inl. (inl. (inl. (inr. u))) ↦ refl (inl. (inl. (inl. (inr. u))) : Fin eight)
  | inl. (inl. (inl. (inl. (inr. u)))) ↦ refl (inl. (inl. (inl. (inl. (inr. u)))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inr. u))))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inr. u))))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. e))))))) ↦ match e [] ]

def quaternion_symmetry_3_equiv : Equiv (Fin eight) (Fin eight)
  ≔ quasi_inverse_equiv (Fin eight) (Fin eight) quaternion_symmetry_3_map quaternion_symmetry_3_inverse_map quaternion_symmetry_3_equiv_retraction quaternion_symmetry_3_equiv_section

def quaternion_symmetry_3_commutes_a (x : Fin eight)
  : Id (Fin eight) (quaternion_symmetry_3_map (quaternion_a_map x)) (quaternion_a_map (quaternion_symmetry_3_map x))
  ≔ match x [
  | inr. u ↦ refl (inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))) : Fin eight)
  | inl. (inr. u) ↦ refl (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))) : Fin eight)
  | inl. (inl. (inr. u)) ↦ refl (inl. (inl. (inl. (inl. (inr. u)))) : Fin eight)
  | inl. (inl. (inl. (inr. u))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inr. u))))) : Fin eight)
  | inl. (inl. (inl. (inl. (inr. u)))) ↦ refl (inl. (inl. (inr. u)) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inr. u))))) ↦ refl (inl. (inl. (inl. (inr. u))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))) ↦ refl (inr. u : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))) ↦ refl (inl. (inr. u) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. e))))))) ↦ match e [] ]

def quaternion_symmetry_3_commutes_b (x : Fin eight)
  : Id (Fin eight) (quaternion_symmetry_3_map (quaternion_b_map x)) (quaternion_b_map (quaternion_symmetry_3_map x))
  ≔ match x [
  | inr. u ↦ refl (inr. u : Fin eight)
  | inl. (inr. u) ↦ refl (inl. (inl. (inl. (inl. (inl. (inr. u))))) : Fin eight)
  | inl. (inl. (inr. u)) ↦ refl (inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))) : Fin eight)
  | inl. (inl. (inl. (inr. u))) ↦ refl (inl. (inl. (inl. (inr. u))) : Fin eight)
  | inl. (inl. (inl. (inl. (inr. u)))) ↦ refl (inl. (inl. (inl. (inl. (inr. u)))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inr. u))))) ↦ refl (inl. (inr. u) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))) ↦ refl (inl. (inl. (inr. u)) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. e))))))) ↦ match e [] ]

def quaternion_symmetry_3 : BicycleIsomorphisms quaternion_bicycle quaternion_bicycle
  ≔ (quaternion_symmetry_3_equiv, (quaternion_symmetry_3_commutes_a, quaternion_symmetry_3_commutes_b))

{` The symmetry sending 0 to 4. `}
def quaternion_symmetry_4_map : Fin eight → Fin eight ≔ [
  | inr. u ↦ inl. (inl. (inl. (inl. (inr. u))))
  | inl. (inr. u) ↦ inl. (inl. (inl. (inl. (inl. (inr. u)))))
  | inl. (inl. (inr. u)) ↦ inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))
  | inl. (inl. (inl. (inr. u))) ↦ inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))))
  | inl. (inl. (inl. (inl. (inr. u)))) ↦ inr. u
  | inl. (inl. (inl. (inl. (inl. (inr. u))))) ↦ inl. (inr. u)
  | inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))) ↦ inl. (inl. (inr. u))
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))) ↦ inl. (inl. (inl. (inr. u)))
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. e))))))) ↦ match e [] ]

def quaternion_symmetry_4_inverse_map : Fin eight → Fin eight ≔ [
  | inr. u ↦ inl. (inl. (inl. (inl. (inr. u))))
  | inl. (inr. u) ↦ inl. (inl. (inl. (inl. (inl. (inr. u)))))
  | inl. (inl. (inr. u)) ↦ inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))
  | inl. (inl. (inl. (inr. u))) ↦ inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))))
  | inl. (inl. (inl. (inl. (inr. u)))) ↦ inr. u
  | inl. (inl. (inl. (inl. (inl. (inr. u))))) ↦ inl. (inr. u)
  | inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))) ↦ inl. (inl. (inr. u))
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))) ↦ inl. (inl. (inl. (inr. u)))
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. e))))))) ↦ match e [] ]

def quaternion_symmetry_4_equiv_retraction (x : Fin eight)
  : Id (Fin eight) (quaternion_symmetry_4_inverse_map (quaternion_symmetry_4_map x)) x
  ≔ match x [
  | inr. u ↦ refl (inr. u : Fin eight)
  | inl. (inr. u) ↦ refl (inl. (inr. u) : Fin eight)
  | inl. (inl. (inr. u)) ↦ refl (inl. (inl. (inr. u)) : Fin eight)
  | inl. (inl. (inl. (inr. u))) ↦ refl (inl. (inl. (inl. (inr. u))) : Fin eight)
  | inl. (inl. (inl. (inl. (inr. u)))) ↦ refl (inl. (inl. (inl. (inl. (inr. u)))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inr. u))))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inr. u))))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. e))))))) ↦ match e [] ]

def quaternion_symmetry_4_equiv_section (x : Fin eight)
  : Id (Fin eight) (quaternion_symmetry_4_map (quaternion_symmetry_4_inverse_map x)) x
  ≔ match x [
  | inr. u ↦ refl (inr. u : Fin eight)
  | inl. (inr. u) ↦ refl (inl. (inr. u) : Fin eight)
  | inl. (inl. (inr. u)) ↦ refl (inl. (inl. (inr. u)) : Fin eight)
  | inl. (inl. (inl. (inr. u))) ↦ refl (inl. (inl. (inl. (inr. u))) : Fin eight)
  | inl. (inl. (inl. (inl. (inr. u)))) ↦ refl (inl. (inl. (inl. (inl. (inr. u)))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inr. u))))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inr. u))))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. e))))))) ↦ match e [] ]

def quaternion_symmetry_4_equiv : Equiv (Fin eight) (Fin eight)
  ≔ quasi_inverse_equiv (Fin eight) (Fin eight) quaternion_symmetry_4_map quaternion_symmetry_4_inverse_map quaternion_symmetry_4_equiv_retraction quaternion_symmetry_4_equiv_section

def quaternion_symmetry_4_commutes_a (x : Fin eight)
  : Id (Fin eight) (quaternion_symmetry_4_map (quaternion_a_map x)) (quaternion_a_map (quaternion_symmetry_4_map x))
  ≔ match x [
  | inr. u ↦ refl (inl. (inl. (inl. (inl. (inl. (inr. u))))) : Fin eight)
  | inl. (inr. u) ↦ refl (inr. u : Fin eight)
  | inl. (inl. (inr. u)) ↦ refl (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))) : Fin eight)
  | inl. (inl. (inl. (inr. u))) ↦ refl (inl. (inl. (inr. u)) : Fin eight)
  | inl. (inl. (inl. (inl. (inr. u)))) ↦ refl (inl. (inr. u) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inr. u))))) ↦ refl (inl. (inl. (inl. (inl. (inr. u)))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))) ↦ refl (inl. (inl. (inl. (inr. u))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. e))))))) ↦ match e [] ]

def quaternion_symmetry_4_commutes_b (x : Fin eight)
  : Id (Fin eight) (quaternion_symmetry_4_map (quaternion_b_map x)) (quaternion_b_map (quaternion_symmetry_4_map x))
  ≔ match x [
  | inr. u ↦ refl (inl. (inl. (inl. (inr. u))) : Fin eight)
  | inl. (inr. u) ↦ refl (inl. (inl. (inr. u)) : Fin eight)
  | inl. (inl. (inr. u)) ↦ refl (inl. (inl. (inl. (inl. (inl. (inr. u))))) : Fin eight)
  | inl. (inl. (inl. (inr. u))) ↦ refl (inl. (inl. (inl. (inl. (inr. u)))) : Fin eight)
  | inl. (inl. (inl. (inl. (inr. u)))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inr. u))))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))) ↦ refl (inl. (inr. u) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))) ↦ refl (inr. u : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. e))))))) ↦ match e [] ]

def quaternion_symmetry_4 : BicycleIsomorphisms quaternion_bicycle quaternion_bicycle
  ≔ (quaternion_symmetry_4_equiv, (quaternion_symmetry_4_commutes_a, quaternion_symmetry_4_commutes_b))

{` The symmetry sending 0 to 5. `}
def quaternion_symmetry_5_map : Fin eight → Fin eight ≔ [
  | inr. u ↦ inl. (inl. (inl. (inl. (inl. (inr. u)))))
  | inl. (inr. u) ↦ inr. u
  | inl. (inl. (inr. u)) ↦ inl. (inl. (inl. (inr. u)))
  | inl. (inl. (inl. (inr. u))) ↦ inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))
  | inl. (inl. (inl. (inl. (inr. u)))) ↦ inl. (inr. u)
  | inl. (inl. (inl. (inl. (inl. (inr. u))))) ↦ inl. (inl. (inl. (inl. (inr. u))))
  | inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))) ↦ inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))))
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))) ↦ inl. (inl. (inr. u))
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. e))))))) ↦ match e [] ]

def quaternion_symmetry_5_inverse_map : Fin eight → Fin eight ≔ [
  | inr. u ↦ inl. (inr. u)
  | inl. (inr. u) ↦ inl. (inl. (inl. (inl. (inr. u))))
  | inl. (inl. (inr. u)) ↦ inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))))
  | inl. (inl. (inl. (inr. u))) ↦ inl. (inl. (inr. u))
  | inl. (inl. (inl. (inl. (inr. u)))) ↦ inl. (inl. (inl. (inl. (inl. (inr. u)))))
  | inl. (inl. (inl. (inl. (inl. (inr. u))))) ↦ inr. u
  | inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))) ↦ inl. (inl. (inl. (inr. u)))
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))) ↦ inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. e))))))) ↦ match e [] ]

def quaternion_symmetry_5_equiv_retraction (x : Fin eight)
  : Id (Fin eight) (quaternion_symmetry_5_inverse_map (quaternion_symmetry_5_map x)) x
  ≔ match x [
  | inr. u ↦ refl (inr. u : Fin eight)
  | inl. (inr. u) ↦ refl (inl. (inr. u) : Fin eight)
  | inl. (inl. (inr. u)) ↦ refl (inl. (inl. (inr. u)) : Fin eight)
  | inl. (inl. (inl. (inr. u))) ↦ refl (inl. (inl. (inl. (inr. u))) : Fin eight)
  | inl. (inl. (inl. (inl. (inr. u)))) ↦ refl (inl. (inl. (inl. (inl. (inr. u)))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inr. u))))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inr. u))))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. e))))))) ↦ match e [] ]

def quaternion_symmetry_5_equiv_section (x : Fin eight)
  : Id (Fin eight) (quaternion_symmetry_5_map (quaternion_symmetry_5_inverse_map x)) x
  ≔ match x [
  | inr. u ↦ refl (inr. u : Fin eight)
  | inl. (inr. u) ↦ refl (inl. (inr. u) : Fin eight)
  | inl. (inl. (inr. u)) ↦ refl (inl. (inl. (inr. u)) : Fin eight)
  | inl. (inl. (inl. (inr. u))) ↦ refl (inl. (inl. (inl. (inr. u))) : Fin eight)
  | inl. (inl. (inl. (inl. (inr. u)))) ↦ refl (inl. (inl. (inl. (inl. (inr. u)))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inr. u))))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inr. u))))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. e))))))) ↦ match e [] ]

def quaternion_symmetry_5_equiv : Equiv (Fin eight) (Fin eight)
  ≔ quasi_inverse_equiv (Fin eight) (Fin eight) quaternion_symmetry_5_map quaternion_symmetry_5_inverse_map quaternion_symmetry_5_equiv_retraction quaternion_symmetry_5_equiv_section

def quaternion_symmetry_5_commutes_a (x : Fin eight)
  : Id (Fin eight) (quaternion_symmetry_5_map (quaternion_a_map x)) (quaternion_a_map (quaternion_symmetry_5_map x))
  ≔ match x [
  | inr. u ↦ refl (inr. u : Fin eight)
  | inl. (inr. u) ↦ refl (inl. (inr. u) : Fin eight)
  | inl. (inl. (inr. u)) ↦ refl (inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))) : Fin eight)
  | inl. (inl. (inl. (inr. u))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))) : Fin eight)
  | inl. (inl. (inl. (inl. (inr. u)))) ↦ refl (inl. (inl. (inl. (inl. (inr. u)))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inr. u))))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inr. u))))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))) ↦ refl (inl. (inl. (inr. u)) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))) ↦ refl (inl. (inl. (inl. (inr. u))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. e))))))) ↦ match e [] ]

def quaternion_symmetry_5_commutes_b (x : Fin eight)
  : Id (Fin eight) (quaternion_symmetry_5_map (quaternion_b_map x)) (quaternion_b_map (quaternion_symmetry_5_map x))
  ≔ match x [
  | inr. u ↦ refl (inl. (inl. (inr. u)) : Fin eight)
  | inl. (inr. u) ↦ refl (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))) : Fin eight)
  | inl. (inl. (inr. u)) ↦ refl (inr. u : Fin eight)
  | inl. (inl. (inl. (inr. u))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inr. u))))) : Fin eight)
  | inl. (inl. (inl. (inl. (inr. u)))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inr. u))))) ↦ refl (inl. (inl. (inl. (inr. u))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))) ↦ refl (inl. (inl. (inl. (inl. (inr. u)))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))) ↦ refl (inl. (inr. u) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. e))))))) ↦ match e [] ]

def quaternion_symmetry_5 : BicycleIsomorphisms quaternion_bicycle quaternion_bicycle
  ≔ (quaternion_symmetry_5_equiv, (quaternion_symmetry_5_commutes_a, quaternion_symmetry_5_commutes_b))

{` The symmetry sending 0 to 6. `}
def quaternion_symmetry_6_map : Fin eight → Fin eight ≔ [
  | inr. u ↦ inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))
  | inl. (inr. u) ↦ inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))))
  | inl. (inl. (inr. u)) ↦ inr. u
  | inl. (inl. (inl. (inr. u))) ↦ inl. (inr. u)
  | inl. (inl. (inl. (inl. (inr. u)))) ↦ inl. (inl. (inr. u))
  | inl. (inl. (inl. (inl. (inl. (inr. u))))) ↦ inl. (inl. (inl. (inr. u)))
  | inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))) ↦ inl. (inl. (inl. (inl. (inr. u))))
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))) ↦ inl. (inl. (inl. (inl. (inl. (inr. u)))))
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. e))))))) ↦ match e [] ]

def quaternion_symmetry_6_inverse_map : Fin eight → Fin eight ≔ [
  | inr. u ↦ inl. (inl. (inr. u))
  | inl. (inr. u) ↦ inl. (inl. (inl. (inr. u)))
  | inl. (inl. (inr. u)) ↦ inl. (inl. (inl. (inl. (inr. u))))
  | inl. (inl. (inl. (inr. u))) ↦ inl. (inl. (inl. (inl. (inl. (inr. u)))))
  | inl. (inl. (inl. (inl. (inr. u)))) ↦ inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))
  | inl. (inl. (inl. (inl. (inl. (inr. u))))) ↦ inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))))
  | inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))) ↦ inr. u
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))) ↦ inl. (inr. u)
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. e))))))) ↦ match e [] ]

def quaternion_symmetry_6_equiv_retraction (x : Fin eight)
  : Id (Fin eight) (quaternion_symmetry_6_inverse_map (quaternion_symmetry_6_map x)) x
  ≔ match x [
  | inr. u ↦ refl (inr. u : Fin eight)
  | inl. (inr. u) ↦ refl (inl. (inr. u) : Fin eight)
  | inl. (inl. (inr. u)) ↦ refl (inl. (inl. (inr. u)) : Fin eight)
  | inl. (inl. (inl. (inr. u))) ↦ refl (inl. (inl. (inl. (inr. u))) : Fin eight)
  | inl. (inl. (inl. (inl. (inr. u)))) ↦ refl (inl. (inl. (inl. (inl. (inr. u)))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inr. u))))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inr. u))))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. e))))))) ↦ match e [] ]

def quaternion_symmetry_6_equiv_section (x : Fin eight)
  : Id (Fin eight) (quaternion_symmetry_6_map (quaternion_symmetry_6_inverse_map x)) x
  ≔ match x [
  | inr. u ↦ refl (inr. u : Fin eight)
  | inl. (inr. u) ↦ refl (inl. (inr. u) : Fin eight)
  | inl. (inl. (inr. u)) ↦ refl (inl. (inl. (inr. u)) : Fin eight)
  | inl. (inl. (inl. (inr. u))) ↦ refl (inl. (inl. (inl. (inr. u))) : Fin eight)
  | inl. (inl. (inl. (inl. (inr. u)))) ↦ refl (inl. (inl. (inl. (inl. (inr. u)))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inr. u))))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inr. u))))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. e))))))) ↦ match e [] ]

def quaternion_symmetry_6_equiv : Equiv (Fin eight) (Fin eight)
  ≔ quasi_inverse_equiv (Fin eight) (Fin eight) quaternion_symmetry_6_map quaternion_symmetry_6_inverse_map quaternion_symmetry_6_equiv_retraction quaternion_symmetry_6_equiv_section

def quaternion_symmetry_6_commutes_a (x : Fin eight)
  : Id (Fin eight) (quaternion_symmetry_6_map (quaternion_a_map x)) (quaternion_a_map (quaternion_symmetry_6_map x))
  ≔ match x [
  | inr. u ↦ refl (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))) : Fin eight)
  | inl. (inr. u) ↦ refl (inl. (inl. (inr. u)) : Fin eight)
  | inl. (inl. (inr. u)) ↦ refl (inl. (inr. u) : Fin eight)
  | inl. (inl. (inl. (inr. u))) ↦ refl (inl. (inl. (inl. (inl. (inr. u)))) : Fin eight)
  | inl. (inl. (inl. (inl. (inr. u)))) ↦ refl (inl. (inl. (inl. (inr. u))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inr. u))))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inr. u))))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))) ↦ refl (inr. u : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. e))))))) ↦ match e [] ]

def quaternion_symmetry_6_commutes_b (x : Fin eight)
  : Id (Fin eight) (quaternion_symmetry_6_map (quaternion_b_map x)) (quaternion_b_map (quaternion_symmetry_6_map x))
  ≔ match x [
  | inr. u ↦ refl (inl. (inl. (inl. (inl. (inl. (inr. u))))) : Fin eight)
  | inl. (inr. u) ↦ refl (inl. (inl. (inl. (inl. (inr. u)))) : Fin eight)
  | inl. (inl. (inr. u)) ↦ refl (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))) : Fin eight)
  | inl. (inl. (inl. (inr. u))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))) : Fin eight)
  | inl. (inl. (inl. (inl. (inr. u)))) ↦ refl (inl. (inr. u) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inr. u))))) ↦ refl (inr. u : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))) ↦ refl (inl. (inl. (inl. (inr. u))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))) ↦ refl (inl. (inl. (inr. u)) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. e))))))) ↦ match e [] ]

def quaternion_symmetry_6 : BicycleIsomorphisms quaternion_bicycle quaternion_bicycle
  ≔ (quaternion_symmetry_6_equiv, (quaternion_symmetry_6_commutes_a, quaternion_symmetry_6_commutes_b))

{` The symmetry sending 0 to 7. `}
def quaternion_symmetry_7_map : Fin eight → Fin eight ≔ [
  | inr. u ↦ inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))))
  | inl. (inr. u) ↦ inl. (inl. (inr. u))
  | inl. (inl. (inr. u)) ↦ inl. (inl. (inl. (inl. (inl. (inr. u)))))
  | inl. (inl. (inl. (inr. u))) ↦ inr. u
  | inl. (inl. (inl. (inl. (inr. u)))) ↦ inl. (inl. (inl. (inr. u)))
  | inl. (inl. (inl. (inl. (inl. (inr. u))))) ↦ inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))
  | inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))) ↦ inl. (inr. u)
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))) ↦ inl. (inl. (inl. (inl. (inr. u))))
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. e))))))) ↦ match e [] ]

def quaternion_symmetry_7_inverse_map : Fin eight → Fin eight ≔ [
  | inr. u ↦ inl. (inl. (inl. (inr. u)))
  | inl. (inr. u) ↦ inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))
  | inl. (inl. (inr. u)) ↦ inl. (inr. u)
  | inl. (inl. (inl. (inr. u))) ↦ inl. (inl. (inl. (inl. (inr. u))))
  | inl. (inl. (inl. (inl. (inr. u)))) ↦ inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))))
  | inl. (inl. (inl. (inl. (inl. (inr. u))))) ↦ inl. (inl. (inr. u))
  | inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))) ↦ inl. (inl. (inl. (inl. (inl. (inr. u)))))
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))) ↦ inr. u
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. e))))))) ↦ match e [] ]

def quaternion_symmetry_7_equiv_retraction (x : Fin eight)
  : Id (Fin eight) (quaternion_symmetry_7_inverse_map (quaternion_symmetry_7_map x)) x
  ≔ match x [
  | inr. u ↦ refl (inr. u : Fin eight)
  | inl. (inr. u) ↦ refl (inl. (inr. u) : Fin eight)
  | inl. (inl. (inr. u)) ↦ refl (inl. (inl. (inr. u)) : Fin eight)
  | inl. (inl. (inl. (inr. u))) ↦ refl (inl. (inl. (inl. (inr. u))) : Fin eight)
  | inl. (inl. (inl. (inl. (inr. u)))) ↦ refl (inl. (inl. (inl. (inl. (inr. u)))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inr. u))))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inr. u))))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. e))))))) ↦ match e [] ]

def quaternion_symmetry_7_equiv_section (x : Fin eight)
  : Id (Fin eight) (quaternion_symmetry_7_map (quaternion_symmetry_7_inverse_map x)) x
  ≔ match x [
  | inr. u ↦ refl (inr. u : Fin eight)
  | inl. (inr. u) ↦ refl (inl. (inr. u) : Fin eight)
  | inl. (inl. (inr. u)) ↦ refl (inl. (inl. (inr. u)) : Fin eight)
  | inl. (inl. (inl. (inr. u))) ↦ refl (inl. (inl. (inl. (inr. u))) : Fin eight)
  | inl. (inl. (inl. (inl. (inr. u)))) ↦ refl (inl. (inl. (inl. (inl. (inr. u)))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inr. u))))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inr. u))))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. e))))))) ↦ match e [] ]

def quaternion_symmetry_7_equiv : Equiv (Fin eight) (Fin eight)
  ≔ quasi_inverse_equiv (Fin eight) (Fin eight) quaternion_symmetry_7_map quaternion_symmetry_7_inverse_map quaternion_symmetry_7_equiv_retraction quaternion_symmetry_7_equiv_section

def quaternion_symmetry_7_commutes_a (x : Fin eight)
  : Id (Fin eight) (quaternion_symmetry_7_map (quaternion_a_map x)) (quaternion_a_map (quaternion_symmetry_7_map x))
  ≔ match x [
  | inr. u ↦ refl (inl. (inl. (inr. u)) : Fin eight)
  | inl. (inr. u) ↦ refl (inl. (inl. (inl. (inr. u))) : Fin eight)
  | inl. (inl. (inr. u)) ↦ refl (inr. u : Fin eight)
  | inl. (inl. (inl. (inr. u))) ↦ refl (inl. (inr. u) : Fin eight)
  | inl. (inl. (inl. (inl. (inr. u)))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inr. u))))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))) ↦ refl (inl. (inl. (inl. (inl. (inr. u)))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inr. u))))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. e))))))) ↦ match e [] ]

def quaternion_symmetry_7_commutes_b (x : Fin eight)
  : Id (Fin eight) (quaternion_symmetry_7_map (quaternion_b_map x)) (quaternion_b_map (quaternion_symmetry_7_map x))
  ≔ match x [
  | inr. u ↦ refl (inl. (inl. (inl. (inl. (inr. u)))) : Fin eight)
  | inl. (inr. u) ↦ refl (inl. (inr. u) : Fin eight)
  | inl. (inl. (inr. u)) ↦ refl (inl. (inl. (inr. u)) : Fin eight)
  | inl. (inl. (inl. (inr. u))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))) : Fin eight)
  | inl. (inl. (inl. (inl. (inr. u)))) ↦ refl (inr. u : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inr. u))))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inr. u))))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))) ↦ refl (inl. (inl. (inl. (inr. u))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. e))))))) ↦ match e [] ]

def quaternion_symmetry_7 : BicycleIsomorphisms quaternion_bicycle quaternion_bicycle
  ≔ (quaternion_symmetry_7_equiv, (quaternion_symmetry_7_commutes_a, quaternion_symmetry_7_commutes_b))

def quaternion_symmetry_from_zero (z : Fin eight)
  : BookFiber (Id Bicycles quaternion_bicycle quaternion_bicycle) (Fin eight)
      (bicycle_evaluation quaternion_bicycle (inr. star.)) z
  ≔ match z [
  | inr. star. ↦ (bicycle_path_from_iso quaternion_bicycle quaternion_bicycle quaternion_symmetry_0,
      refl (inr. star. : Fin eight))
  | inl. (inr. star.) ↦ (bicycle_path_from_iso quaternion_bicycle quaternion_bicycle quaternion_symmetry_1,
      refl (inl. (inr. star.) : Fin eight))
  | inl. (inl. (inr. star.)) ↦ (bicycle_path_from_iso quaternion_bicycle quaternion_bicycle quaternion_symmetry_2,
      refl (inl. (inl. (inr. star.)) : Fin eight))
  | inl. (inl. (inl. (inr. star.))) ↦ (bicycle_path_from_iso quaternion_bicycle quaternion_bicycle quaternion_symmetry_3,
      refl (inl. (inl. (inl. (inr. star.))) : Fin eight))
  | inl. (inl. (inl. (inl. (inr. star.)))) ↦ (bicycle_path_from_iso quaternion_bicycle quaternion_bicycle quaternion_symmetry_4,
      refl (inl. (inl. (inl. (inl. (inr. star.)))) : Fin eight))
  | inl. (inl. (inl. (inl. (inl. (inr. star.))))) ↦ (bicycle_path_from_iso quaternion_bicycle quaternion_bicycle quaternion_symmetry_5,
      refl (inl. (inl. (inl. (inl. (inl. (inr. star.))))) : Fin eight))
  | inl. (inl. (inl. (inl. (inl. (inl. (inr. star.)))))) ↦ (bicycle_path_from_iso quaternion_bicycle quaternion_bicycle quaternion_symmetry_6,
      refl (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.)))))) : Fin eight))
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.))))))) ↦ (bicycle_path_from_iso quaternion_bicycle quaternion_bicycle quaternion_symmetry_7,
      refl (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.))))))) : Fin eight))
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. e))))))) ↦ match e [] ]

{` group.tex 2093: the quaternion bicycle is normal. `}
def quaternion_bicycle_normal : IsNormalBicycle quaternion_bicycle
  ≔ normal_bicycle_from_point_surjective quaternion_bicycle (inr. star.)
      (z ↦ mere (BookFiber (Id Bicycles quaternion_bicycle quaternion_bicycle) (Fin eight)
          (bicycle_evaluation quaternion_bicycle (inr. star.)) z)
        (quaternion_symmetry_from_zero z))

{` Litmus: USym Q₈ ≃ Fin 8 (evaluation at 0), so Q₈ is finite with 8 symmetries. `}
def quaternion_usym_equiv : Equiv (USym quaternion_group) (Fin eight)
  ≔ compose_equiv (USym quaternion_group) (Id Bicycles quaternion_bicycle quaternion_bicycle) (Fin eight)
      (automorphism_group_usym_equiv Bicycles bicycles_groupoid quaternion_bicycle)
      (native_equivalence (Id Bicycles quaternion_bicycle quaternion_bicycle) (Fin eight)
        (bicycle_evaluation_equiv quaternion_bicycle quaternion_bicycle_normal (inr. star.)))

def quaternion_group_finite : IsFiniteGroup quaternion_group
  ≔ mere (Σ Nat (k ↦ Id Type (USym quaternion_group) (Fin k)))
      (eight, ua (USym quaternion_group) (Fin eight) quaternion_usym_equiv)

def quaternion_group_card : Id Nat (group_card quaternion_group quaternion_group_finite) eight
  ≔ cardinality_from_path (USym quaternion_group) quaternion_group_finite eight
      (ua (USym quaternion_group) (Fin eight) quaternion_usym_equiv)
