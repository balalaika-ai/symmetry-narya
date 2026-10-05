export "75-modular-successor"

def finite_standard_period (n : Nat) : PositiveCyclePeriod (finite_standard_cycle n) n
  ≔ cycle_period_from_point (Remainder (suc. n)) (remainder_set (suc. n)) (modular_successor_equiv n)
      (modular_successor_cyclic n) (remainder_at n zero. star.) (pos. (suc. n))
      (concat (Remainder (suc. n))
        (modular_successor n (iterate (Remainder (suc. n)) (modular_successor n) n (remainder_at n zero. star.)))
        (modular_successor n (remainder_at n n (le_refl n))) (remainder_at n zero. star.)
        (refl (modular_successor n) (modular_successor_iterate n n (le_refl n))) (modular_successor_last n))

def finite_standard_no_smaller_period (n k : Nat) (small : Lt k n)
  (period : PositiveCyclePeriod (finite_standard_cycle n) k) : Empty
  ≔ let p : Id (Remainder (suc. n))
      (iterate (Remainder (suc. n)) (modular_successor n) (suc. k) (remainder_at n zero. star.))
      (remainder_at n zero. star.) ≔ period (refl (remainder_at n zero. star.)) in
    nat_encode (suc. k) zero. (calc
      (suc. k : Nat) = iterate (Remainder (suc. n)) (modular_successor n) (suc. k) (remainder_at n zero. star.) .fst
        by modular_successor_iterate n (suc. k) small .fst
      = zero. by p .fst ∎)

def finite_standard_period_lower (n k : Nat) (period : PositiveCyclePeriod (finite_standard_cycle n) k) : Le n k
  ≔ match le_total n k [
  | inl. h ↦ h
  | inr. h ↦ match le_split k n h [
    | inl. small ↦ match finite_standard_no_smaller_period n k small period []
    | inr. eq ↦ le_from_equal n k (inverse Nat k n eq) ] ]

def finite_standard_minimum (n : Nat) : IsMinimum (PositiveCyclePeriod (finite_standard_cycle n)) n
  ≔ (finite_standard_period n, k period ↦ le_to_book n k (finite_standard_period_lower n k period))

def finite_standard_periods (n : Nat)
  : Id (Subtypes Int) (CyclePeriods (finite_standard_cycle n)) (Multiples (suc. n))
  ≔ least_cycle_periods_multiples (finite_standard_cycle n) n (finite_standard_minimum n)

def cycle_remainder_commutes (c : Cycles) (n : Nat) (period : PositiveCyclePeriod c n) (a : c .fst .fst .fst)
  : Commutes (Remainder (suc. n)) (c .fst .fst .fst) (modular_successor_equiv n) (c .fst .snd)
      (cycle_remainder_map c (suc. n) a)
  ≔ r ↦ inverse (c .fst .fst .fst)
      (c .fst .snd .map (cycle_remainder_map c (suc. n) a r))
      (cycle_remainder_map c (suc. n) a (modular_successor n r))
      (cycle_power_division c (suc. n) period (pos. (suc. (r .fst)))
        (integer_euclidean_division (pos. (suc. (r .fst))) (suc. n) (lt_to_book zero. (suc. n) star.)) a)

def finite_cycle_isomorphism (c : Cycles) (n : Nat) (minimal : IsMinimum (PositiveCyclePeriod c) n)
  (a : c .fst .fst .fst) : PermutationIsomorphisms (finite_standard_cycle n .fst) (c .fst)
  ≔ (cycle_remainder_equiv c n minimal a, cycle_remainder_commutes c n (minimal .fst) a)

def finite_cycle_path (c : Cycles) (n : Nat) (minimal : IsMinimum (PositiveCyclePeriod c) n)
  (a : c .fst .fst .fst) : Id Cycles (finite_standard_cycle n) c
  ≔ equiv_inverse_map (Id Cycles (finite_standard_cycle n) c)
      (PermutationIsomorphisms (finite_standard_cycle n .fst) (c .fst))
      (cycle_paths_equiv (finite_standard_cycle n) c) (finite_cycle_isomorphism c n minimal a)

def finite_cycle_component (c : Cycles) (n : Nat) (minimal : IsMinimum (PositiveCyclePeriod c) n)
  : Mere (Id Cycles c (finite_standard_cycle n))
  ≔ trunc_map native_truncation (c .fst .fst .fst) (Id Cycles c (finite_standard_cycle n))
      (a ↦ inverse Cycles (finite_standard_cycle n) c (finite_cycle_path c n minimal a)) (c .snd .fst)

def finite_cycle_order (n : Nat) : Order ≔ cycle_order (finite_standard_cycle n)

def cycle_minimum_order (c : Cycles) (n : Nat) (minimal : IsMinimum (PositiveCyclePeriod c) n)
  : Id Order (cycle_order c) (finite_cycle_order n)
  ≔ equiv_inverse_map (Id Order (cycle_order c) (finite_cycle_order n))
      (Mere (Id Cycles c (finite_standard_cycle n))) (set_trunc_paths Cycles c (finite_standard_cycle n))
      (finite_cycle_component c n minimal)

{` The positive index suc n represents the cycle of size n+1; zero is the
   infinite cycle.  This convention agrees with the book's principal orders. `}
def principal_cycle (n : Nat) : Cycles
  ≔ match n [ zero. ↦ infinite_cycle | suc. n ↦ finite_standard_cycle n ]

def principal_order (n : Nat) : Order ≔ cycle_order (principal_cycle n)

def lpo_cycle_classification (lpo : LimitedOmniscience) (c : DecidableCycles)
  : Σ Nat (n ↦ Mere (Id Cycles (c .fst) (principal_cycle n)))
  ≔ match lpo_cycle_period_alternative lpo c [
  | inl. m ↦ (suc. (m .fst), finite_cycle_component (c .fst) (m .fst) (m .snd))
  | inr. h ↦ (zero., set_trunc_paths Cycles (c .fst) infinite_cycle .map h) ]
