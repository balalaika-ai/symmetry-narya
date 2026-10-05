export "71-limited-omniscience"

def DecidableCycles : Type ≔ Σ Cycles (c ↦ DecidableEquality (c .fst .fst .fst))

def cycle_period_decidable (c : Cycles) (d : DecidableEquality (c .fst .fst .fst)) (n : Int)
  : Decidable (CyclePeriods c n .fst)
  ≔ mere_rec (c .fst .fst .fst) (Decidable (CyclePeriods c n .fst))
      (decidability_prop (CyclePeriods c n .fst) (CyclePeriods c n .snd))
      (x ↦ match d (permutation_power (c .fst .fst .fst) (c .fst .snd) n x) x [
      | inl. p ↦ inl. (cycle_period_from_point (c .fst .fst .fst) (c .fst .fst .snd) (c .fst .snd) (c .snd) x n p)
      | inr. no ↦ inr. (p ↦ no (p (refl x))) ]) (c .snd .fst)

def PositiveCyclePeriod (c : Cycles) (k : Nat) : Type ≔ CyclePeriods c (pos. (suc. k)) .fst
def ZeroPeriods : Subtypes Int ≔ n ↦ (Id Int n int_zero, int_set n int_zero)

def zero_is_period (c : Cycles) (n : Int) (p : Id Int n int_zero) : CyclePeriods c n .fst
  ≔ transport Int (PowerPeriod (c .fst .fst .fst) (c .fst .snd)) int_zero n (inverse Int n int_zero p)
      (power_period_zero (c .fst .fst .fst) (c .fst .snd))

def no_positive_period_is_zero (c : Cycles) (no : (k : Nat) → PositiveCyclePeriod c k → Empty)
  (n : Int) (p : CyclePeriods c n .fst) : Id Int n int_zero
  ≔ match n [
  | pos. zero. ↦ refl int_zero
  | pos. (suc. k) ↦ absurd (Id Int (pos. (suc. k)) int_zero) (no k p)
  | neg. k ↦ absurd (Id Int (neg. k) int_zero)
      (no k (power_period_neg (c .fst .fst .fst) (c .fst .snd) (neg. k) p)) ]

def no_positive_periods_trivial (c : Cycles) (no : (k : Nat) → PositiveCyclePeriod c k → Empty)
  : Id (Subtypes Int) (CyclePeriods c) ZeroPeriods
  ≔ funext Int (_ ↦ PropTypes) (CyclePeriods c) ZeroPeriods
      (n ↦ proposition_extensionality (CyclePeriods c n) (ZeroPeriods n)
        (no_positive_period_is_zero c no n) (zero_is_period c n))

def infinite_period_is_zero (n : Int) (p : CyclePeriods infinite_cycle n .fst) : Id Int n int_zero
  ≔ concat Int n (int_add int_zero n) int_zero
      (inverse Int (int_add int_zero n) n (int_add_zero_left n)) (p (refl int_zero))

def infinite_cycle_periods : Id (Subtypes Int) (CyclePeriods infinite_cycle) ZeroPeriods
  ≔ funext Int (_ ↦ PropTypes) (CyclePeriods infinite_cycle) ZeroPeriods
      (n ↦ proposition_extensionality (CyclePeriods infinite_cycle n) (ZeroPeriods n)
        (infinite_period_is_zero n) (zero_is_period infinite_cycle n))

def no_positive_periods_infinite_order (c : Cycles) (no : (k : Nat) → PositiveCyclePeriod c k → Empty)
  : Id Order (cycle_order c) infinite_order
  ≔ order_periods_injective (cycle_order c) infinite_order
      (concat (Subtypes Int) (CyclePeriods c) ZeroPeriods (CyclePeriods infinite_cycle)
        (no_positive_periods_trivial c no)
        (inverse (Subtypes Int) (CyclePeriods infinite_cycle) ZeroPeriods infinite_cycle_periods))

def no_positive_periods_infinite_component (c : Cycles) (no : (k : Nat) → PositiveCyclePeriod c k → Empty)
  : Mere (Id Cycles c infinite_cycle)
  ≔ set_trunc_paths Cycles c infinite_cycle .map (no_positive_periods_infinite_order c no)

def CyclePeriodAlternative (c : Cycles) : Type
  ≔ Sum (Σ Nat (IsMinimum (PositiveCyclePeriod c))) (Id Order (cycle_order c) infinite_order)

{` The finite-order branch is completed by the subsequent division argument.
   Here LPO is used only as the explicitly supplied parameter. `}
def lpo_cycle_period_alternative (lpo : LimitedOmniscience) (c : DecidableCycles)
  : CyclePeriodAlternative (c .fst)
  ≔ match lpo_decidable_search lpo (PositiveCyclePeriod (c .fst))
      (k ↦ cycle_period_decidable (c .fst) (c .snd) (pos. (suc. k))) [
  | inl. m ↦ inl. m
  | inr. no ↦ inr. (no_positive_periods_infinite_order (c .fst) no) ]
