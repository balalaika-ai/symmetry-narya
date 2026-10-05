export "473-bicycle-stabilizers"

{` def:Dinfty-Q (group.tex 1955–1990) and the claims around it: the standard
   infinite dihedral bicycle (Z ⊔ Z, a, b) and the standard quaternion
   bicycle (Fin 8, a, b) are bicycles, D∞ and Q₈ are their automorphism
   groups, and neither satisfies ab = ba (group.tex 2043–2046). `}

{` a(inl n) = inl (n+1), a(inr n) = inr (n−1), b swaps the summands.
   (n+1 = int_add n 1 and n−1 = int_sub n 1 reduce to int_succ n and
   int_pred n by definition.) `}
def dihedral_a_map : Sum Int Int → Sum Int Int
  ≔ [ inl. n ↦ inl. (int_add n (pos. (suc. zero.))) | inr. n ↦ inr. (int_sub n (pos. (suc. zero.))) ]

def dihedral_a_inverse_map : Sum Int Int → Sum Int Int
  ≔ [ inl. n ↦ inl. (int_pred n) | inr. n ↦ inr. (int_succ n) ]

def dihedral_a_retraction (x : Sum Int Int) : Id (Sum Int Int) (dihedral_a_inverse_map (dihedral_a_map x)) x
  ≔ match x [ inl. n ↦ inl. (int_pred_succ n) | inr. n ↦ inr. (int_succ_pred n) ]

def dihedral_a_section (x : Sum Int Int) : Id (Sum Int Int) (dihedral_a_map (dihedral_a_inverse_map x)) x
  ≔ match x [ inl. n ↦ inl. (int_succ_pred n) | inr. n ↦ inr. (int_pred_succ n) ]

def dihedral_a_equiv : Equiv (Sum Int Int) (Sum Int Int)
  ≔ quasi_inverse_equiv (Sum Int Int) (Sum Int Int) dihedral_a_map dihedral_a_inverse_map
      dihedral_a_retraction dihedral_a_section

def dihedral_b_map : Sum Int Int → Sum Int Int ≔ [ inl. n ↦ inr. n | inr. n ↦ inl. n ]

def dihedral_b_involutive (x : Sum Int Int) : Id (Sum Int Int) (dihedral_b_map (dihedral_b_map x)) x
  ≔ match x [ inl. n ↦ refl (inl. n : Sum Int Int) | inr. n ↦ refl (inr. n : Sum Int Int) ]

def dihedral_b_equiv : Equiv (Sum Int Int) (Sum Int Int)
  ≔ quasi_inverse_equiv (Sum Int Int) (Sum Int Int) dihedral_b_map dihedral_b_map
      dihedral_b_involutive dihedral_b_involutive

def dihedral_a_unfold (n : Int)
  : Id (Product (Sum Int Int) (Sum Int Int)) (dihedral_a_map (inl. n), dihedral_a_map (inr. n))
      (inl. (int_succ n), inr. (int_pred n))
  ≔ refl ((inl. (int_succ n), inr. (int_pred n)) : Product (Sum Int Int) (Sum Int Int))

def dihedral_set : isSet (Sum Int Int) ≔ sum_set Int Int int_set int_set

{` aⁿ(inl m) = inl (m + n). `}
def dihedral_a_power_left (n m : Int)
  : Id (Sum Int Int) (permutation_power (Sum Int Int) dihedral_a_equiv n (inl. m)) (inl. (int_add m n))
  ≔ inverse (Sum Int Int) (inl. (int_add m n)) (permutation_power (Sum Int Int) dihedral_a_equiv n (inl. m))
      (permutation_power_intertwine Int (Sum Int Int) int_succ_equiv dihedral_a_equiv (k ↦ inl. k)
        (k ↦ refl (inl. (int_succ k) : Sum Int Int)) n m)

{` Every element is ⟦ℓ⟧(inl 0): inl n = aⁿ(inl 0), inr n = b(aⁿ(inl 0)). `}
def dihedral_word_from_origin (y : Sum Int Int)
  : BicycleWordFrom (Sum Int Int) dihedral_a_equiv dihedral_b_equiv (inl. int_zero) y
  ≔ match y [
  | inl. n ↦ (cons. (inl. n) nil., calc
      (inl. n : Sum Int Int) = inl. (int_add int_zero n) by inl. (inverse Int (int_add int_zero n) n (int_add_zero_left n))
      = permutation_power (Sum Int Int) dihedral_a_equiv n (inl. int_zero)
        by inverse (Sum Int Int) (permutation_power (Sum Int Int) dihedral_a_equiv n (inl. int_zero)) (inl. (int_add int_zero n))
          (dihedral_a_power_left n int_zero) ∎)
  | inr. n ↦ (cons. (inr. (pos. (suc. zero.))) (cons. (inl. n) nil.), calc
      (inr. n : Sum Int Int) = dihedral_b_map (inl. (int_add int_zero n)) by inr. (inverse Int (int_add int_zero n) n (int_add_zero_left n))
      = dihedral_b_map (permutation_power (Sum Int Int) dihedral_a_equiv n (inl. int_zero))
        by refl dihedral_b_map
          (inverse (Sum Int Int) (permutation_power (Sum Int Int) dihedral_a_equiv n (inl. int_zero)) (inl. (int_add int_zero n))
            (dihedral_a_power_left n int_zero)) ∎) ]

def dihedral_bicycle_connected : BicycleConnected (Sum Int Int) dihedral_a_equiv dihedral_b_equiv
  ≔ bicycle_connected_from_point (Sum Int Int) dihedral_a_equiv dihedral_b_equiv (inl. int_zero)
      (y ↦ mere (BicycleWordFrom (Sum Int Int) dihedral_a_equiv dihedral_b_equiv (inl. int_zero) y)
        (dihedral_word_from_origin y))

{` def:Dinfty-Q: the standard infinite dihedral bicycle and D∞ ≔ Aut_Bicyc(Z ⊔ Z, a, b). `}
def infinite_dihedral_bicycle : Bicycles
  ≔ mkbicycle (Sum Int Int, dihedral_set) dihedral_a_equiv dihedral_b_equiv dihedral_bicycle_connected

def infinite_dihedral_group : Group ≔ bicycle_automorphism_group infinite_dihedral_bicycle

{` group.tex 2043–2046: the infinite dihedral bicycle does not satisfy ab = ba:
   ab(inl 0) = inr (−1) but ba(inl 0) = inr 1. `}
def dihedral_negative_right_code : Sum Int Int → Type
  ≔ [ inl. _ ↦ Empty | inr. (pos. _) ↦ Empty | inr. (neg. _) ↦ Unit ]

def dihedral_not_commuting
  (h : Id (Sum Int Int → Sum Int Int) (x ↦ dihedral_a_map (dihedral_b_map x)) (x ↦ dihedral_b_map (dihedral_a_map x)))
  : Empty
  ≔ transport (Sum Int Int) dihedral_negative_right_code
      (dihedral_a_map (dihedral_b_map (inl. int_zero))) (dihedral_b_map (dihedral_a_map (inl. int_zero)))
      (refl ((f ↦ f (inl. int_zero)) : (Sum Int Int → Sum Int Int) → Sum Int Int) h) star.

{` The quaternion bicycle. `}
def eight : Nat ≔ suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. zero.)))))))

{` a(k) = k+1 for even k, k+3 for odd k (mod 8), as printed. `}
def quaternion_a_map : Fin eight → Fin eight ≔ [
  | inr. u ↦ inl. (inr. u)
  | inl. (inr. u) ↦ inl. (inl. (inl. (inl. (inr. u))))
  | inl. (inl. (inr. u)) ↦ inl. (inl. (inl. (inr. u)))
  | inl. (inl. (inl. (inr. u))) ↦ inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))
  | inl. (inl. (inl. (inl. (inr. u)))) ↦ inl. (inl. (inl. (inl. (inl. (inr. u)))))
  | inl. (inl. (inl. (inl. (inl. (inr. u))))) ↦ inr. u
  | inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))) ↦ inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))))
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))) ↦ inl. (inl. (inr. u))
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. e))))))) ↦ match e [] ]

def quaternion_a_inverse_map : Fin eight → Fin eight ≔ [
  | inr. u ↦ inl. (inl. (inl. (inl. (inl. (inr. u)))))
  | inl. (inr. u) ↦ inr. u
  | inl. (inl. (inr. u)) ↦ inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))))
  | inl. (inl. (inl. (inr. u))) ↦ inl. (inl. (inr. u))
  | inl. (inl. (inl. (inl. (inr. u)))) ↦ inl. (inr. u)
  | inl. (inl. (inl. (inl. (inl. (inr. u))))) ↦ inl. (inl. (inl. (inl. (inr. u))))
  | inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))) ↦ inl. (inl. (inl. (inr. u)))
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))) ↦ inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. e))))))) ↦ match e [] ]

def quaternion_a_equiv_retraction (x : Fin eight)
  : Id (Fin eight) (quaternion_a_inverse_map (quaternion_a_map x)) x
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

def quaternion_a_equiv_section (x : Fin eight)
  : Id (Fin eight) (quaternion_a_map (quaternion_a_inverse_map x)) x
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

def quaternion_a_equiv : Equiv (Fin eight) (Fin eight)
  ≔ quasi_inverse_equiv (Fin eight) (Fin eight) quaternion_a_map quaternion_a_inverse_map quaternion_a_equiv_retraction quaternion_a_equiv_section

{` b(k) = k−1 for even k, k−3 for odd k (mod 8), as printed. `}
def quaternion_b_map : Fin eight → Fin eight ≔ [
  | inr. u ↦ inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))))
  | inl. (inr. u) ↦ inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))
  | inl. (inl. (inr. u)) ↦ inl. (inr. u)
  | inl. (inl. (inl. (inr. u))) ↦ inr. u
  | inl. (inl. (inl. (inl. (inr. u)))) ↦ inl. (inl. (inl. (inr. u)))
  | inl. (inl. (inl. (inl. (inl. (inr. u))))) ↦ inl. (inl. (inr. u))
  | inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))) ↦ inl. (inl. (inl. (inl. (inl. (inr. u)))))
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))) ↦ inl. (inl. (inl. (inl. (inr. u))))
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. e))))))) ↦ match e [] ]

def quaternion_b_inverse_map : Fin eight → Fin eight ≔ [
  | inr. u ↦ inl. (inl. (inl. (inr. u)))
  | inl. (inr. u) ↦ inl. (inl. (inr. u))
  | inl. (inl. (inr. u)) ↦ inl. (inl. (inl. (inl. (inl. (inr. u)))))
  | inl. (inl. (inl. (inr. u))) ↦ inl. (inl. (inl. (inl. (inr. u))))
  | inl. (inl. (inl. (inl. (inr. u)))) ↦ inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))))
  | inl. (inl. (inl. (inl. (inl. (inr. u))))) ↦ inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))
  | inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))) ↦ inl. (inr. u)
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))) ↦ inr. u
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. e))))))) ↦ match e [] ]

def quaternion_b_equiv_retraction (x : Fin eight)
  : Id (Fin eight) (quaternion_b_inverse_map (quaternion_b_map x)) x
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

def quaternion_b_equiv_section (x : Fin eight)
  : Id (Fin eight) (quaternion_b_map (quaternion_b_inverse_map x)) x
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

def quaternion_b_equiv : Equiv (Fin eight) (Fin eight)
  ≔ quasi_inverse_equiv (Fin eight) (Fin eight) quaternion_b_map quaternion_b_inverse_map quaternion_b_equiv_retraction quaternion_b_equiv_section

{` Every element is ⟦ℓ⟧(0) for an explicit word: aⁱ(0) or aⁱ(b(0)), i < 4. `}
def quaternion_word_from_zero (y : Fin eight)
  : BicycleWordFrom (Fin eight) quaternion_a_equiv quaternion_b_equiv (inr. star.) y
  ≔ match y [
  | inr. star. ↦ (cons. (inl. (pos. zero.)) nil., refl (inr. star. : Fin eight))
  | inl. (inr. star.) ↦ (cons. (inl. (pos. (suc. zero.))) nil., refl (inl. (inr. star.) : Fin eight))
  | inl. (inl. (inr. star.)) ↦ (cons. (inl. (pos. (suc. zero.))) (cons. (inr. (pos. (suc. zero.))) nil.), refl (inl. (inl. (inr. star.)) : Fin eight))
  | inl. (inl. (inl. (inr. star.))) ↦ (cons. (inl. (pos. (suc. (suc. zero.)))) (cons. (inr. (pos. (suc. zero.))) nil.), refl (inl. (inl. (inl. (inr. star.))) : Fin eight))
  | inl. (inl. (inl. (inl. (inr. star.)))) ↦ (cons. (inl. (pos. (suc. (suc. zero.)))) nil., refl (inl. (inl. (inl. (inl. (inr. star.)))) : Fin eight))
  | inl. (inl. (inl. (inl. (inl. (inr. star.))))) ↦ (cons. (inl. (pos. (suc. (suc. (suc. zero.))))) nil., refl (inl. (inl. (inl. (inl. (inl. (inr. star.))))) : Fin eight))
  | inl. (inl. (inl. (inl. (inl. (inl. (inr. star.)))))) ↦ (cons. (inl. (pos. (suc. (suc. (suc. zero.))))) (cons. (inr. (pos. (suc. zero.))) nil.), refl (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.)))))) : Fin eight))
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.))))))) ↦ (cons. (inl. (pos. zero.)) (cons. (inr. (pos. (suc. zero.))) nil.), refl (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. star.))))))) : Fin eight))
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. e))))))) ↦ match e [] ]

def quaternion_bicycle_connected : BicycleConnected (Fin eight) quaternion_a_equiv quaternion_b_equiv
  ≔ bicycle_connected_from_point (Fin eight) quaternion_a_equiv quaternion_b_equiv (inr. star.)
      (y ↦ mere (BicycleWordFrom (Fin eight) quaternion_a_equiv quaternion_b_equiv (inr. star.) y) (quaternion_word_from_zero y))

{` def:Dinfty-Q, second part: the standard quaternion bicycle (Fin 8, a, b)
   and Q₈ ≔ Aut_Bicyc(Fin 8, a, b). Fin 8 is the book's 8 (def:finiteset),
   with k encoded as inl^k(inr ⋆). `}
def quaternion_bicycle : Bicycles
  ≔ mkbicycle (Fin eight, fin_set eight) quaternion_a_equiv quaternion_b_equiv quaternion_bicycle_connected

def quaternion_group : Group ≔ bicycle_automorphism_group quaternion_bicycle

{` Litmus checks: what the printed a, b satisfy. a⁴ = b⁴ = id, a² = b² (= k ↦ k+4) ≠ id,
   bab⁻¹ = a⁻¹, aba = b, and ab ≠ ba ((ab)(0) = 2, (ba)(0) = 6). `}
def quaternion_a_order_four (x : Fin eight)
  : Id (Fin eight) (permutation_power (Fin eight) quaternion_a_equiv (pos. (suc. (suc. (suc. (suc. zero.))))) x) x
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

def quaternion_b_order_four (x : Fin eight)
  : Id (Fin eight) (permutation_power (Fin eight) quaternion_b_equiv (pos. (suc. (suc. (suc. (suc. zero.))))) x) x
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

def quaternion_a_square_b_square (x : Fin eight)
  : Id (Fin eight) (permutation_power (Fin eight) quaternion_a_equiv (pos. (suc. (suc. zero.))) x)
      (permutation_power (Fin eight) quaternion_b_equiv (pos. (suc. (suc. zero.))) x)
  ≔ match x [
  | inr. u ↦ refl (inl. (inl. (inl. (inl. (inr. u)))) : Fin eight)
  | inl. (inr. u) ↦ refl (inl. (inl. (inl. (inl. (inl. (inr. u))))) : Fin eight)
  | inl. (inl. (inr. u)) ↦ refl (inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))) : Fin eight)
  | inl. (inl. (inl. (inr. u))) ↦ refl (inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))) : Fin eight)
  | inl. (inl. (inl. (inl. (inr. u)))) ↦ refl (inr. u : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inr. u))))) ↦ refl (inl. (inr. u) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inr. u)))))) ↦ refl (inl. (inl. (inr. u)) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. u))))))) ↦ refl (inl. (inl. (inl. (inr. u))) : Fin eight)
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. e))))))) ↦ match e [] ]

def quaternion_b_conjugates_a (x : Fin eight)
  : Id (Fin eight) (quaternion_b_map (quaternion_a_map (quaternion_b_inverse_map x))) (quaternion_a_inverse_map x)
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

def quaternion_aba (x : Fin eight)
  : Id (Fin eight) (quaternion_a_map (quaternion_b_map (quaternion_a_map x))) (quaternion_b_map x)
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

def fin8_is_two : Fin eight → Type ≔ [
  | inr. _ ↦ Empty
  | inl. (inr. _) ↦ Empty
  | inl. (inl. (inr. _)) ↦ Unit
  | inl. (inl. (inl. (inr. _))) ↦ Empty
  | inl. (inl. (inl. (inl. (inr. _)))) ↦ Empty
  | inl. (inl. (inl. (inl. (inl. (inr. _))))) ↦ Empty
  | inl. (inl. (inl. (inl. (inl. (inl. (inr. _)))))) ↦ Empty
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. _))))))) ↦ Empty
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. e))))))) ↦ match e [] ]

def fin8_is_four : Fin eight → Type ≔ [
  | inr. _ ↦ Empty
  | inl. (inr. _) ↦ Empty
  | inl. (inl. (inr. _)) ↦ Empty
  | inl. (inl. (inl. (inr. _))) ↦ Empty
  | inl. (inl. (inl. (inl. (inr. _)))) ↦ Unit
  | inl. (inl. (inl. (inl. (inl. (inr. _))))) ↦ Empty
  | inl. (inl. (inl. (inl. (inl. (inl. (inr. _)))))) ↦ Empty
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inr. _))))))) ↦ Empty
  | inl. (inl. (inl. (inl. (inl. (inl. (inl. (inl. e))))))) ↦ match e [] ]

def quaternion_a_square_not_identity
  (h : Id (Fin eight) (permutation_power (Fin eight) quaternion_a_equiv (pos. (suc. (suc. zero.))) (inr. star.)) (inr. star.)) : Empty
  ≔ transport (Fin eight) fin8_is_four (permutation_power (Fin eight) quaternion_a_equiv (pos. (suc. (suc. zero.))) (inr. star.)) (inr. star.) h star.

def quaternion_not_commuting
  (h : Id (Fin eight → Fin eight) (x ↦ quaternion_a_map (quaternion_b_map x)) (x ↦ quaternion_b_map (quaternion_a_map x))) : Empty
  ≔ transport (Fin eight) fin8_is_two (quaternion_a_map (quaternion_b_map (inr. star.))) (quaternion_b_map (quaternion_a_map (inr. star.)))
      (refl ((f ↦ f (inr. star.)) : (Fin eight → Fin eight) → Fin eight) h) star.
