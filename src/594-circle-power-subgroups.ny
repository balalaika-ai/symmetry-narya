export "505-gset-core-litmus"

{` ex:Rm0-subgroup: the Z-sets R_m (m > 0) and R of chapter 3 as subgroups of
   Z = mkgroup(S¹, base) (circle_group C, for any circle C).

   R_m = power_circle_family C n (m = n+1; R_m(base) = Fin m only through the
   circle β-identification, so the point 0 is power_bundle_zero), transitive
   because Tot(R_m) is connected (power_bundle_connected). A symmetry p of base
   fixes 0 iff p = loop^{mk} for some integer k (rmsub_picks_out): with
   T = R_m(loop), p · 0 = T^{w(p)}(0) (w the winding number), the monodromy
   (R_m(base), T) = (Fin m, s) (power_circle_monodromy) makes (R_m(base), T)
   a cycle whose periods are the multiples of m.

   R = circle_integer_family C (as a family of sets, code_is_set), pointed at
   0 = code_root, transitive since Tot(R) is contractible; R(loop^k)(0) = k
   (code_encode_power), and the only symmetry fixing 0 is refl
   (rsub_picks_out). `}

def rmsub_gset (C : CircleSignature) (n : Nat) : GSet (circle_group C) ≔ power_circle_family C n

def RmBase (C : CircleSignature) (n : Nat) : Type ≔ power_circle_family C n (C .base) .fst

def rmsub_point (C : CircleSignature) (n : Nat) : RmBase C n ≔ power_bundle_zero C n

def rmsub_transitive (C : CircleSignature) (n : Nat) : IsTransitive (circle_group C) (rmsub_gset C n)
  ≔ connected_action_type_transitive (circle_group C) (rmsub_gset C n) (power_bundle_connected C n)

{` ex:Rm0-subgroup: (R_m, 0) : Sub(Z). `}
def rmsub_subgroup (C : CircleSignature) (n : Nat) : Subgroups (circle_group C)
  ≔ (rmsub_gset C n, rmsub_point C n, rmsub_transitive C n)

{` T = R_m(loop) on R_m(base). `}
def rmsub_loop_equiv (C : CircleSignature) (n : Nat) : Equiv (RmBase C n) (RmBase C n)
  ≔ gset_act_equiv (circle_group C) (rmsub_gset C n) (C .base) (C .base) (C .loop)

def rmsub_power_act (C : CircleSignature) (n : Nat) (z : Int) (x : RmBase C n)
  : Id (RmBase C n) (gset_usym_act (circle_group C) (rmsub_gset C n) (loop_power (C .carrier) (C .base) (C .loop) z) x)
      (permutation_power (RmBase C n) (rmsub_loop_equiv C n) z x)
  ≔ let T ≔ rmsub_loop_equiv C n in
    transport_loop_power (C .carrier) (u ↦ power_circle_family C n u .fst) (C .base) (C .loop)
      (k ↦ permutation_power (RmBase C n) T k x)
      (k ↦ inverse (RmBase C n) (permutation_power (RmBase C n) T (int_succ k) x) (T .map (permutation_power (RmBase C n) T k x))
        (permutation_power_succ (RmBase C n) T k x)) z

{` The monodromy (R_m(base), T) = (Fin m, s). `}
def rmsub_monodromy (C : CircleSignature) (n : Nat)
  : Id Permutations (power_circle_family C n (C .base), rmsub_loop_equiv C n) (power_fiber_set n, finite_fin_successor n)
  ≔ power_circle_monodromy C n

def rmsub_cyclic (C : CircleSignature) (n : Nat) : Cyclic (RmBase C n) (rmsub_loop_equiv C n)
  ≔ transport Permutations (p ↦ Cyclic (p .fst .fst) (p .snd)) (power_fiber_set n, finite_fin_successor n)
      (power_circle_family C n (C .base), rmsub_loop_equiv C n)
      (inverse Permutations (power_circle_family C n (C .base), rmsub_loop_equiv C n) (power_fiber_set n, finite_fin_successor n)
        (rmsub_monodromy C n))
      (finite_fin_successor_cyclic n)

def rmsub_fin_periods (n : Nat) : Id (Subtypes Int) (CyclePeriods (finite_fin_cycle n)) (Multiples (suc. n))
  ≔ concat (Subtypes Int) (CyclePeriods (finite_fin_cycle n)) (CyclePeriods (finite_standard_cycle n)) (Multiples (suc. n))
      (cycle_paths_imply_periods (finite_fin_cycle n) (finite_standard_cycle n)
        (mere (Id Cycles (finite_fin_cycle n) (finite_standard_cycle n)) (fin_remainder_cycle_path n)))
      (finite_standard_periods n)

{` z is a period of T iff m divides z. `}
def rmsub_period_multiple (C : CircleSignature) (n : Nat) (z : Int)
  (p : PowerPeriod (RmBase C n) (rmsub_loop_equiv C n) z) : Multiples (suc. n) z .fst
  ≔ transport (Subtypes Int) (H ↦ H z .fst) (CyclePeriods (finite_fin_cycle n)) (Multiples (suc. n)) (rmsub_fin_periods n)
      (transport Permutations (q ↦ PowerPeriod (q .fst .fst) (q .snd) z)
        (power_circle_family C n (C .base), rmsub_loop_equiv C n) (power_fiber_set n, finite_fin_successor n)
        (rmsub_monodromy C n) p)

def rmsub_multiple_period (C : CircleSignature) (n : Nat) (z : Int) (h : Multiples (suc. n) z .fst)
  : PowerPeriod (RmBase C n) (rmsub_loop_equiv C n) z
  ≔ transport Permutations (q ↦ PowerPeriod (q .fst .fst) (q .snd) z)
      (power_fiber_set n, finite_fin_successor n) (power_circle_family C n (C .base), rmsub_loop_equiv C n)
      (inverse Permutations (power_circle_family C n (C .base), rmsub_loop_equiv C n) (power_fiber_set n, finite_fin_successor n)
        (rmsub_monodromy C n))
      (transport (Subtypes Int) (H ↦ H z .fst) (Multiples (suc. n)) (CyclePeriods (finite_fin_cycle n))
        (inverse (Subtypes Int) (CyclePeriods (finite_fin_cycle n)) (Multiples (suc. n)) (rmsub_fin_periods n)) h)

def rmsub_base_set (C : CircleSignature) (n : Nat) : isSet (RmBase C n) ≔ power_circle_family C n (C .base) .snd

{` ex:Rm0-subgroup: the symmetries p of base that keep 0 in place are exactly
   the loop^{mk}. `}
def rmsub_picks_out (C : CircleSignature) (n : Nat) (g : USym (circle_group C))
  : Equiv (Id (RmBase C n) (gset_usym_act (circle_group C) (rmsub_gset C n) g (rmsub_point C n)) (rmsub_point C n))
      (Mere (Σ Int (k ↦ Id (USym (circle_group C)) g (loop_power (C .carrier) (C .base) (C .loop) (int_mul k (pos. (suc. n)))))))
  ≔ let Z ≔ circle_group C in
    let X ≔ rmsub_gset C n in
    let x0 ≔ rmsub_point C n in
    let A ≔ RmBase C n in
    let T ≔ rmsub_loop_equiv C n in
    let lp ≔ loop_power (C .carrier) (C .base) (C .loop) in
    let K ≔ Σ Int (k ↦ Id (USym Z) g (lp (int_mul k (pos. (suc. n))))) in
    let act ≔ ((h ↦ gset_usym_act Z X h x0) : USym Z → A) in
    let w ≔ circle_winding C g in
    let gw : Id (USym Z) (lp w) g ≔ circle_power_winding C g in
    iff_equiv (Id A (act g) x0) (Mere K) (rmsub_base_set C n (act g) x0) (mere_isprop K)
      (h ↦ let tw : Id A (permutation_power A T w x0) x0
             ≔ concat A (permutation_power A T w x0) (act (lp w)) x0
                 (inverse A (act (lp w)) (permutation_power A T w x0) (rmsub_power_act C n w x0))
                 (concat A (act (lp w)) (act g) x0 (refl act gw) h) in
           mere_rec (MultipleWitness (suc. n) w) (Mere K) (mere_isprop K)
             (v ↦ mere K (v .fst, concat (USym Z) g (lp w) (lp (int_mul (v .fst) (pos. (suc. n))))
               (inverse (USym Z) (lp w) g gw) (refl lp (v .snd))))
             (rmsub_period_multiple C n w (cycle_period_from_point A (rmsub_base_set C n) T (rmsub_cyclic C n) x0 w tw)))
      (m ↦ mere_rec K (Id A (act g) x0) (rmsub_base_set C n (act g) x0)
        (v ↦ let z ≔ int_mul (v .fst) (pos. (suc. n)) in
             concat A (act g) (act (lp z)) x0 (refl act (v .snd))
               (concat A (act (lp z)) (permutation_power A T z x0) x0 (rmsub_power_act C n z x0)
                 (rmsub_multiple_period C n z (mere (MultipleWitness (suc. n) z) (v .fst, refl z)) (refl x0)))) m)

{` The Z-set R, R(base) = Z, R(loop) = succ. `}
def rsub_family (C : CircleSignature) (z : C .carrier) : Type ≔ circle_integer_family C z

def rsub_gset (C : CircleSignature) : GSet (circle_group C)
  ≔ z ↦ (circle_integer_family C z, code_is_set C (circle_integer_family C) (circle_integer_monodromy C) z)

def rsub_point (C : CircleSignature) : circle_integer_family C (C .base)
  ≔ code_root C (circle_integer_family C) (circle_integer_monodromy C)

def rsub_transitive (C : CircleSignature) : IsTransitive (circle_group C) (rsub_gset C)
  ≔ connected_action_type_transitive (circle_group C) (rsub_gset C)
      (contractible_connected (Σ (C .carrier) (circle_integer_family C)) (circle_integer_total_contractible C))

{` ex:Rm0-subgroup, case m = 0: (R, 0) : Sub(Z). `}
def rsub_subgroup (C : CircleSignature) : Subgroups (circle_group C) ≔ (rsub_gset C, rsub_point C, rsub_transitive C)

{` R(loop^k)(0) = k. `}
def rsub_power_act (C : CircleSignature) (k : Int)
  : Id (circle_integer_family C (C .base))
      (gset_usym_act (circle_group C) (rsub_gset C) (loop_power (C .carrier) (C .base) (C .loop) k) (rsub_point C))
      (circle_integer_monodromy C .enumeration .map k)
  ≔ code_encode_power C (circle_integer_family C) (circle_integer_monodromy C) k

{` The only symmetry keeping 0 in place is refl. `}
def rsub_picks_out (C : CircleSignature) (g : USym (circle_group C))
  : Equiv (Id (circle_integer_family C (C .base)) (gset_usym_act (circle_group C) (rsub_gset C) g (rsub_point C)) (rsub_point C))
      (Id (USym (circle_group C)) g (refl (C .base)))
  ≔ let R ≔ circle_integer_family C in
    let m ≔ circle_integer_monodromy C in
    let enc ≔ code_encode C R m (C .base) in
    let x0 ≔ rsub_point C in
    let hs ≔ code_is_set C R m (C .base) in
    iff_equiv (Id (R (C .base)) (enc g) x0) (Id (USym (circle_group C)) g (refl (C .base)))
      (hs (enc g) x0) (usym_set (circle_group C) g (refl (C .base)))
      (h ↦ equivalence_injective (Id (C .carrier) (C .base) (C .base)) (R (C .base)) (circle_path_code_equiv C R m (C .base))
        g (refl (C .base))
        (concat (R (C .base)) (enc g) x0 (enc (refl (C .base))) h
          (inverse (R (C .base)) (enc (refl (C .base))) x0 (transport_refl (C .carrier) R (C .base) x0))))
      (e ↦ concat (R (C .base)) (enc g) (enc (refl (C .base))) x0 (refl enc e) (transport_refl (C .carrier) R (C .base) x0))
