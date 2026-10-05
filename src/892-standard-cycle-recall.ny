export "807-generalized-dihedral-groups"
export "77-decidable-orders"

{` Chapter 8 (congp.tex 50-58): the recall of def:standard-cycle before
   def:gen-dihedral and its footnote.

   Line 50: C_n is Aut_Cyc(Z/~_n, s) (order_cyclic_group, module 807), where
   ~_n is "z - z' is a period of n"; for EVERY cycle (T, t) of order n this
   holds iff t^z = t^{z'} (order_relation_powers), and the standard cycle is
   such a cycle (standard_cycle_order), so "any/all" agree
   (order_relation_any, order_relation_all).

   Line 54 (footnote): for n = principal_order 0 (infinite) the map of cycles
   (Z, s) → (Z/~_n, s), z ↦ [z], is an equivalence; for n = principal_order (m+1)
   it factors through Fin (m+1) (z ↦ the remainder of z), and the induced map
   (Fin (m+1), s) → (Z/~_n, s), k ↦ s^k[0], is an equivalence of cycles. The
   LPO part is chapter 3's classification of decidable orders
   (lpo_decidable_orders_equiv). `}

def src_power (c : Cycles) (z : Int) : c .fst .fst .fst → c .fst .fst .fst
  ≔ permutation_power (c .fst .fst .fst) (c .fst .snd) z

def src_power_eq_of_period (c : Cycles) (z z' : Int) (p : PowerPeriod (c .fst .fst .fst) (c .fst .snd) (int_sub z z'))
  : Id (c .fst .fst .fst → c .fst .fst .fst) (src_power c z) (src_power c z')
  ≔ let T ≔ c .fst .fst .fst in
    funext T (_ ↦ T) (src_power c z) (src_power c z') (x ↦ calc
      src_power c z x = src_power c (int_add (int_sub z z') z') x
        by refl ((k ↦ src_power c k x) : Int → T) (inverse Int (int_add (int_sub z z') z') z (int_sub_add z z'))
      = src_power c z' (src_power c (int_sub z z') x) by permutation_power_add T (c .fst .snd) (int_sub z z') z' x
      = src_power c z' x by refl (src_power c z') (p (refl x)) ∎)

def src_period_of_power_eq (c : Cycles) (z z' : Int)
  (e : Id (c .fst .fst .fst → c .fst .fst .fst) (src_power c z) (src_power c z'))
  : PowerPeriod (c .fst .fst .fst) (c .fst .snd) (int_sub z z')
  ≔ let T ≔ c .fst .fst .fst in
    funext T (_ ↦ T) (src_power c (int_sub z z')) (identity T) (x ↦ calc
      src_power c (int_add z (int_neg z')) x = src_power c (int_neg z') (src_power c z x)
        by permutation_power_add T (c .fst .snd) z (int_neg z') x
      = src_power c (int_neg z') (src_power c z' x) by refl (src_power c (int_neg z')) (e (refl x))
      = src_power c (int_add z' (int_neg z')) x
        by inverse T (src_power c (int_add z' (int_neg z')) x) (src_power c (int_neg z') (src_power c z' x))
          (permutation_power_add T (c .fst .snd) z' (int_neg z') x)
      = src_power c int_zero x by refl ((k ↦ src_power c k x) : Int → T) (int_sub_self z')
      = x by refl x ∎)

{` Line 50: for a cycle (T, t) of order n, z ~_n z' iff t^z = t^{z'}. `}
def order_relation_powers (n : Order) (c : Cycles) (h : Id Order (cycle_order c) n) (z z' : Int)
  : Product (SubgroupMember (order_periods n) (int_sub z z')
              → Id (c .fst .fst .fst → c .fst .fst .fst) (src_power c z) (src_power c z'))
      (Id (c .fst .fst .fst → c .fst .fst .fst) (src_power c z) (src_power c z')
              → SubgroupMember (order_periods n) (int_sub z z'))
  ≔ let k ≔ int_sub z z' in
    let F ≔ ((d ↦ SubgroupMember (order_periods d) k) : Order → Type) in
    (s ↦ src_power_eq_of_period c z z' (transport Order F n (cycle_order c) (inverse Order (cycle_order c) n h) s),
     e ↦ transport Order F (cycle_order c) n h (src_period_of_power_eq c z z' e))

{` "for any/all cycles of order n": the relation holds iff t^z = t^{z'} for
   all such cycles, iff it holds for some such cycle (one exists: the
   standard cycle). `}
def order_relation_all (n : Order) (z z' : Int) (s : SubgroupMember (order_periods n) (int_sub z z'))
  (c : Cycles) (h : Id Order (cycle_order c) n)
  : Id (c .fst .fst .fst → c .fst .fst .fst) (src_power c z) (src_power c z')
  ≔ order_relation_powers n c h z z' .fst s

def order_relation_any (n : Order) (z z' : Int)
  (w : Mere (Σ Cycles (c ↦ Product (Id Order (cycle_order c) n)
              (Id (c .fst .fst .fst → c .fst .fst .fst) (src_power c z) (src_power c z')))))
  : SubgroupMember (order_periods n) (int_sub z z')
  ≔ mere_rec (Σ Cycles (c ↦ Product (Id Order (cycle_order c) n)
                (Id (c .fst .fst .fst → c .fst .fst .fst) (src_power c z) (src_power c z'))))
      (SubgroupMember (order_periods n) (int_sub z z')) (order_periods n (int_sub z z') .snd)
      (u ↦ order_relation_powers n (u .fst) (u .snd .fst) z z' .snd (u .snd .snd)) w

def order_relation_standard (n : Order) (z z' : Int) (s : SubgroupMember (order_periods n) (int_sub z z'))
  : Id (standard_cycle n .fst .fst .fst → standard_cycle n .fst .fst .fst)
      (src_power (standard_cycle n) z) (src_power (standard_cycle n) z')
  ≔ order_relation_all n z z' s (standard_cycle n) (standard_cycle_order n)

{` Line 54, infinite case: (Z, s) → (Z/~_n, s), z ↦ [z], is an equivalence of cycles. `}
def src_infinite_H : Subtypes Int ≔ order_periods (principal_order zero.)

def src_infinite_laws : IntegerSubgroupLaws src_infinite_H ≔ order_subgroup_laws (principal_order zero.)

def src_infinite_class_injective
  : PathReflecting Int (SubgroupQuotient src_infinite_H src_infinite_laws) (subgroup_class src_infinite_H src_infinite_laws)
  ≔ z z' p ↦
    let k : SubgroupMember src_infinite_H (int_sub z z')
      ≔ quotient_effective Int (subgroup_relation src_infinite_H src_infinite_laws) z z' .map p in
    calc
      z = int_add (int_sub z z') z' by inverse Int (int_add (int_sub z z') z') z (int_sub_add z z')
      = int_add int_zero z' by refl ((y ↦ int_add y z') : Int → Int) (infinite_period_is_zero (int_sub z z') k)
      = z' by int_add_zero_left z' ∎

def principal_infinite_class_equiv : Equiv Int (SubgroupQuotient src_infinite_H src_infinite_laws)
  ≔ set_bijection_equiv Int (SubgroupQuotient src_infinite_H src_infinite_laws)
      (subgroup_quotient_set src_infinite_H src_infinite_laws) (subgroup_class src_infinite_H src_infinite_laws)
      src_infinite_class_injective (quotient_surjective Int (subgroup_relation src_infinite_H src_infinite_laws))

def principal_infinite_class_commutes
  : Commutes Int (SubgroupQuotient src_infinite_H src_infinite_laws) int_succ_equiv
      (subgroup_successor src_infinite_H src_infinite_laws) (subgroup_class src_infinite_H src_infinite_laws)
  ≔ z ↦ refl (subgroup_class src_infinite_H src_infinite_laws (int_succ z))

{` Line 54, finite case n = principal_order (m+1). `}
def src_finite_cycle (m : Nat) : Cycles ≔ standard_cycle (principal_order (suc. m))

def src_finite_minimum (m : Nat) : IsMinimum (PositiveCyclePeriod (src_finite_cycle m)) m
  ≔ let H ≔ order_periods (principal_order (suc. m)) in
    let h ≔ order_subgroup_laws (principal_order (suc. m)) in
    transport (Subtypes Int) (K ↦ IsMinimum (k ↦ K (pos. (suc. k)) .fst) m) H (CyclePeriods (subgroup_cycle H h))
      (inverse (Subtypes Int) (CyclePeriods (subgroup_cycle H h)) H (subgroup_cycle_periods H h))
      (finite_standard_minimum m)

def src_finite_zero (m : Nat) : src_finite_cycle m .fst .fst .fst
  ≔ subgroup_class (order_periods (principal_order (suc. m))) (order_subgroup_laws (principal_order (suc. m))) int_zero

{` (Fin (m+1), s) → (Z/~_n, s), k ↦ s^k [0], an equivalence of cycles. `}
def principal_finite_fin_equiv (m : Nat) : Equiv (Fin (suc. m)) (src_finite_cycle m .fst .fst .fst)
  ≔ cycle_finite_enumeration (src_finite_cycle m) m (src_finite_minimum m) (src_finite_zero m)

def principal_finite_fin_commutes (m : Nat)
  : Commutes (Fin (suc. m)) (src_finite_cycle m .fst .fst .fst) (finite_fin_successor m) (src_finite_cycle m .fst .snd)
      (principal_finite_fin_equiv m .map)
  ≔ let c ≔ src_finite_cycle m in
    let e ≔ fin_book_below_equiv (suc. m) in
    let E ≔ cycle_remainder_map c (suc. m) (src_finite_zero m) in
    x ↦ concat (c .fst .fst .fst)
      (E (e .map (equiv_inverse_map (Fin (suc. m)) (Remainder (suc. m)) e (modular_successor m (e .map x)))))
      (E (modular_successor m (e .map x))) (c .fst .snd .map (E (e .map x)))
      (refl E (equiv_counit (Fin (suc. m)) (Remainder (suc. m)) e (modular_successor m (e .map x))))
      (cycle_remainder_commutes c m (src_finite_minimum m .fst) (src_finite_zero m) (e .map x))

{` The map Z → Fin (m+1) (remainder of the Euclidean division). `}
def principal_fin_of_int (m : Nat) (z : Int) : Fin (suc. m)
  ≔ let u ≔ integer_euclidean_division z (suc. m) (lt_to_book zero. (suc. m) star.) in
    equiv_inverse_map (Fin (suc. m)) (Remainder (suc. m)) (fin_book_below_equiv (suc. m)) (u .fst .snd, u .snd .fst)

{` z ↦ [z] factors through Fin (m+1). `}
def principal_finite_factorization (m : Nat) (z : Int)
  : Id (src_finite_cycle m .fst .fst .fst)
      (subgroup_class (order_periods (principal_order (suc. m))) (order_subgroup_laws (principal_order (suc. m))) z)
      (principal_finite_fin_equiv m .map (principal_fin_of_int m z))
  ≔ let H ≔ order_periods (principal_order (suc. m)) in
    let h ≔ order_subgroup_laws (principal_order (suc. m)) in
    let c ≔ src_finite_cycle m in
    let A ≔ c .fst .fst .fst in
    let e ≔ fin_book_below_equiv (suc. m) in
    let u ≔ integer_euclidean_division z (suc. m) (lt_to_book zero. (suc. m) star.) in
    let r : Remainder (suc. m) ≔ (u .fst .snd, u .snd .fst) in
    let E ≔ cycle_remainder_map c (suc. m) (src_finite_zero m) in
    calc
      subgroup_class H h z = permutation_power A (c .fst .snd) z (src_finite_zero m) by subgroup_power_zero H h z
      = E r by cycle_power_division c (suc. m) (src_finite_minimum m .fst) z u (src_finite_zero m)
      = E (e .map (equiv_inverse_map (Fin (suc. m)) (Remainder (suc. m)) e r))
        by refl E (inverse (Remainder (suc. m)) (e .map (equiv_inverse_map (Fin (suc. m)) (Remainder (suc. m)) e r)) r
          (equiv_counit (Fin (suc. m)) (Remainder (suc. m)) e r)) ∎
