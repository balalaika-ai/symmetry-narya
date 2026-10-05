export "594-circle-power-subgroups"
export "526-lagrange-construction"

{` xca:lagrange-Z-action-Rm: con:lagrange applied to the infinite group
   Z = mkgroup(S¹, base) and the subgroup (R_m, 0) with underlying group H_m:
   USym Z ≃ Fin m × USym H_m (rmlag_fin_equiv).

   The premiss of con:lagrange is constructed explicitly (no choice): on the
   standard m-cycle (Z/m, s) an element k is reached from 0 by s^k, so x is
   moved to a by s^{a − x}; this is transported to (R_m(base), R_m(loop))
   along the monodromy identification, and loop^z acts as R_m(loop)^z. `}

{` k ≤ n implies s^k(0) = k in Z/(n+1). `}
def rmlag_le_succ (k : Nat) : Le k (suc. k) ≔ match k [ zero. ↦ star. | suc. k' ↦ rmlag_le_succ k' ]

def rmlag_iterate_zero (n : Nat) (k : Nat) (h : Le k n)
  : Id (Remainder (suc. n)) (iterate (Remainder (suc. n)) (modular_successor n) k (remainder_at n zero. star.))
      (remainder_at n k h)
  ≔ match k [
  | zero. ↦ remainder_equal (suc. n) (remainder_at n zero. star.) (remainder_at n zero. h) (refl (zero. : Nat))
  | suc. k' ↦
      let hr : Le k' n ≔ le_trans k' (suc. k') n (rmlag_le_succ k') h in
      concat (Remainder (suc. n))
        (modular_successor n (iterate (Remainder (suc. n)) (modular_successor n) k' (remainder_at n zero. star.)))
        (modular_successor n (remainder_at n k' hr)) (remainder_at n (suc. k') h)
        (refl (modular_successor n) (rmlag_iterate_zero n k' hr))
        (modular_successor_small n k' h hr) ]

def rmlag_position (n : Nat) (x : Remainder (suc. n))
  : Id (Remainder (suc. n)) (permutation_power (Remainder (suc. n)) (modular_successor_equiv n) (pos. (x .fst)) (remainder_at n zero. star.)) x
  ≔ concat (Remainder (suc. n))
      (iterate (Remainder (suc. n)) (modular_successor n) (x .fst) (remainder_at n zero. star.))
      (remainder_at n (x .fst) (lt_from_book (x .fst) (suc. n) (x .snd))) x
      (rmlag_iterate_zero n (x .fst) (lt_from_book (x .fst) (suc. n) (x .snd)))
      (remainder_equal (suc. n) (remainder_at n (x .fst) (lt_from_book (x .fst) (suc. n) (x .snd))) x (refl (x .fst)))

{` For every permutation: any element can be moved to any other by a chosen power. `}
def RmlagChoiceAll (p : Permutations) : Type
  ≔ (a x : p .fst .fst) → Σ Int (z ↦ Id (p .fst .fst) (permutation_power (p .fst .fst) (p .snd) z x) a)

def rmlag_standard_choice (n : Nat) : RmlagChoiceAll (finite_standard_cycle n .fst)
  ≔ a x ↦
    let R ≔ Remainder (suc. n) in
    let e ≔ modular_successor_equiv n in
    let r0 ≔ remainder_at n zero. star. in
    let kx : Int ≔ pos. (x .fst) in
    let ka : Int ≔ pos. (a .fst) in
    (int_add (int_neg kx) ka, calc
      permutation_power R e (int_add (int_neg kx) ka) x
      = permutation_power R e ka (permutation_power R e (int_neg kx) x) by permutation_power_add R e (int_neg kx) ka x
      = permutation_power R e ka (permutation_power R e (int_neg kx) (permutation_power R e kx r0))
        by refl ((y ↦ permutation_power R e ka (permutation_power R e (int_neg kx) y)) : R → R)
             (inverse R (permutation_power R e kx r0) x (rmlag_position n x))
      = permutation_power R e ka r0
        by refl (permutation_power R e ka) (permutation_power_inverse R e kx r0)
      = a by rmlag_position n a ∎)

{` (Z/m, s) = (R_m(base), R_m(loop)). `}
def rmlag_monodromy_path (C : CircleSignature) (n : Nat)
  : Id Permutations (finite_standard_cycle n .fst) (power_circle_family C n (C .base), rmsub_loop_equiv C n)
  ≔ inverse Permutations (power_circle_family C n (C .base), rmsub_loop_equiv C n) (finite_standard_cycle n .fst)
      (concat Permutations (power_circle_family C n (C .base), rmsub_loop_equiv C n) (finite_fin_cycle n .fst)
        (finite_standard_cycle n .fst)
        (rmsub_monodromy C n) (refl ((c ↦ c .fst) : Cycles → Permutations) (fin_remainder_cycle_path n)))

def rmlag_choice_all (C : CircleSignature) (n : Nat) : RmlagChoiceAll (power_circle_family C n (C .base), rmsub_loop_equiv C n)
  ≔ transport Permutations RmlagChoiceAll (finite_standard_cycle n .fst) (power_circle_family C n (C .base), rmsub_loop_equiv C n)
      (rmlag_monodromy_path C n) (rmlag_standard_choice n)

{` The premiss of con:lagrange for (R_m, 0): every x is moved to 0 by a chosen loop^z. `}
def rmlag_choice (C : CircleSignature) (n : Nat) : LagrangeChoice (circle_group C) (rmsub_gset C n) (rmsub_point C n)
  ≔ x ↦
    let c ≔ rmlag_choice_all C n (rmsub_point C n) x in
    (loop_power (C .carrier) (C .base) (C .loop) (c .fst),
     concat (RmBase C n)
       (gset_usym_act (circle_group C) (rmsub_gset C n) (loop_power (C .carrier) (C .base) (C .loop) (c .fst)) x)
       (permutation_power (RmBase C n) (rmsub_loop_equiv C n) (c .fst) x) (rmsub_point C n)
       (rmsub_power_act C n (c .fst) x) (c .snd))

{` con:lagrange: USym Z ≃ R_m(base) × USym H_m. `}
def rmlag_equiv (C : CircleSignature) (n : Nat)
  : Equiv (USym (circle_group C)) (Product (RmBase C n) (USym (subgroup_group (circle_group C) (rmsub_subgroup C n))))
  ≔ lagrange_construction (circle_group C) (rmsub_subgroup C n) (rmlag_choice C n)

{` xca:lagrange-Z-action-Rm: USym Z ≃ Fin m × USym H_m. `}
def rmlag_fin_equiv (C : CircleSignature) (n : Nat)
  : Equiv (USym (circle_group C)) (Product (Fin (suc. n)) (USym (subgroup_group (circle_group C) (rmsub_subgroup C n))))
  ≔ let H ≔ USym (subgroup_group (circle_group C) (rmsub_subgroup C n)) in
    compose_equiv (USym (circle_group C)) (Product (RmBase C n) H) (Product (Fin (suc. n)) H)
      (rmlag_equiv C n)
      (product_equiv (RmBase C n) H (Fin (suc. n)) H (power_base_trivialization C n) (identity_equiv H))

{` The first component is g ↦ g · 0 (con:lagrange). `}
def rmlag_equiv_fst (C : CircleSignature) (n : Nat) (g : USym (circle_group C))
  : Id (RmBase C n) (rmlag_equiv C n .map g .fst) (gset_usym_act (circle_group C) (rmsub_gset C n) g (rmsub_point C n))
  ≔ refl (gset_usym_act (circle_group C) (rmsub_gset C n) g (rmsub_point C n))

{` Litmus: loop^m fixes 0 in R_m; loop moves 0 in R. `}
def rmlag_litmus_loop_m_fixes (C : CircleSignature) (n : Nat)
  : Id (RmBase C n)
      (gset_usym_act (circle_group C) (rmsub_gset C n)
        (loop_power (C .carrier) (C .base) (C .loop) (int_mul (pos. (suc. zero.)) (pos. (suc. n)))) (rmsub_point C n))
      (rmsub_point C n)
  ≔ let g ≔ loop_power (C .carrier) (C .base) (C .loop) (int_mul (pos. (suc. zero.)) (pos. (suc. n))) in
    equiv_inverse_map
      (Id (RmBase C n) (gset_usym_act (circle_group C) (rmsub_gset C n) g (rmsub_point C n)) (rmsub_point C n))
      (Mere (Σ Int (k ↦ Id (USym (circle_group C)) g (loop_power (C .carrier) (C .base) (C .loop) (int_mul k (pos. (suc. n)))))))
      (rmsub_picks_out C n g)
      (mere (Σ Int (k ↦ Id (USym (circle_group C)) g (loop_power (C .carrier) (C .base) (C .loop) (int_mul k (pos. (suc. n))))))
        (pos. (suc. zero.), refl g))

def rsub_litmus_loop_moves (C : CircleSignature)
  (h : Id (circle_integer_family C (C .base)) (gset_usym_act (circle_group C) (rsub_gset C) (C .loop) (rsub_point C)) (rsub_point C))
  : Empty
  ≔ let e : Id (USym (circle_group C)) (C .loop) (refl (C .base)) ≔ rsub_picks_out C (C .loop) .map h in
    let w : Id Int (pos. (suc. zero.)) int_zero
      ≔ concat Int (pos. (suc. zero.)) (circle_winding C (C .loop)) int_zero
          (inverse Int (circle_winding C (C .loop)) (pos. (suc. zero.)) (circle_winding_loop C))
          (concat Int (circle_winding C (C .loop)) (circle_winding C (refl (C .base))) int_zero
            (refl (circle_winding C) e) (circle_winding_refl C)) in
    nat_encode (suc. zero.) zero. (refl ([ pos. k ↦ k | neg. k ↦ k ] : Int → Nat) w)
