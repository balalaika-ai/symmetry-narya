export "73-least-positive-subgroups"

def integer_division_zero_quotient (r m : Nat) : Id Int (integer_division_value int_zero r m) (pos. r)
  ≔ calc
      integer_division_value int_zero r m = pos. (add (mul zero. m) r) by integer_division_value_pos zero. r m
      = pos. (add zero. r) by refl ((q ↦ (pos. (add q r) : Int)) : Nat → Int) (mul_zero_left m)
      = pos. r by refl ((q ↦ (pos. q : Int)) : Nat → Int) (add_zero_left r) ∎

def cycle_power_division (c : Cycles) (m : Nat) (period : CyclePeriods c (pos. m) .fst)
  (z : Int) (u : IntegerDivisionResult z m) (a : c .fst .fst .fst)
  : Id (c .fst .fst .fst)
      (permutation_power (c .fst .fst .fst) (c .fst .snd) z a)
      (permutation_power (c .fst .fst .fst) (c .fst .snd) (pos. (u .fst .snd)) a)
  ≔ let A ≔ c .fst .fst .fst in let e ≔ c .fst .snd in
    let q ≔ int_mul (u .fst .fst) (pos. m) in
    calc
      permutation_power A e z a = permutation_power A e (int_add q (pos. (u .fst .snd))) a
        by refl ((k ↦ permutation_power A e k a) : Int → A) (u .snd .snd)
      = permutation_power A e (pos. (u .fst .snd)) (permutation_power A e q a)
        by permutation_power_add A e q (pos. (u .fst .snd)) a
      = permutation_power A e (pos. (u .fst .snd)) a
        by refl (permutation_power A e (pos. (u .fst .snd)))
          (subgroup_multiple (CyclePeriods c) (cycle_subgroup_laws c) (pos. m) period (u .fst .fst) (refl a)) ∎

def cycle_remainder_map (c : Cycles) (m : Nat) (a : c .fst .fst .fst) (r : Remainder m) : c .fst .fst .fst
  ≔ permutation_power (c .fst .fst .fst) (c .fst .snd) (pos. (r .fst)) a

def cycle_remainder_surjective (c : Cycles) (m : Nat) (positive : BookLt zero. m)
  (period : CyclePeriods c (pos. m) .fst) (a : c .fst .fst .fst)
  : Surjective (Remainder m) (c .fst .fst .fst) (cycle_remainder_map c m a)
  ≔ y ↦ trunc_map native_truncation (OrbitWitness (c .fst .fst .fst) (c .fst .snd) a y)
      (BookFiber (Remainder m) (c .fst .fst .fst) (cycle_remainder_map c m a) y)
      (w ↦ let u ≔ integer_euclidean_division (w .fst) m positive in
        ((u .fst .snd, u .snd .fst),
          concat (c .fst .fst .fst) y (permutation_power (c .fst .fst .fst) (c .fst .snd) (w .fst) a)
            (cycle_remainder_map c m a (u .fst .snd, u .snd .fst))
            (w .snd) (cycle_power_division c m period (w .fst) u a))) (c .snd .snd a y)

def cycle_remainder_injective (c : Cycles) (n : Nat) (minimal : IsMinimum (PositiveCyclePeriod c) n)
  (a : c .fst .fst .fst) : PathReflecting (Remainder (suc. n)) (c .fst .fst .fst) (cycle_remainder_map c (suc. n) a)
  ≔ r s p ↦
    let difference ≔ int_sub (pos. (r .fst)) (pos. (s .fst)) in
    let period ≔ cycle_period_from_point (c .fst .fst .fst) (c .fst .fst .snd) (c .fst .snd) (c .snd) a difference
      (power_equality_difference (c .fst .fst .fst) (c .fst .snd) (pos. (r .fst)) (pos. (s .fst)) a p) in
    let w ≔ least_subgroup_member_multiple (CyclePeriods c) (cycle_subgroup_laws c) n minimal difference period in
    let eq : Id Int (integer_division_value int_zero (r .fst) (suc. n))
      (integer_division_value (w .fst) (s .fst) (suc. n)) ≔ calc
      integer_division_value int_zero (r .fst) (suc. n) = pos. (r .fst) by integer_division_zero_quotient (r .fst) (suc. n)
      = int_add difference (pos. (s .fst)) by int_sub_add (pos. (r .fst)) (pos. (s .fst))
      = integer_division_value (w .fst) (s .fst) (suc. n)
        by refl ((k ↦ int_add k (pos. (s .fst))) : Int → Int) (w .snd) ∎ in
    subtype_equal Nat (r ↦ BookLt r (suc. n)) (r ↦ book_lt_prop r (suc. n)) r s
      (integer_division_equal_pairs int_zero (w .fst) (r .fst) (s .fst) (suc. n) (r .snd) (s .snd) eq .snd)

def cycle_remainder_equiv (c : Cycles) (n : Nat) (minimal : IsMinimum (PositiveCyclePeriod c) n)
  (a : c .fst .fst .fst) : Equiv (Remainder (suc. n)) (c .fst .fst .fst)
  ≔ set_bijection_equiv (Remainder (suc. n)) (c .fst .fst .fst) (c .fst .fst .snd)
      (cycle_remainder_map c (suc. n) a) (cycle_remainder_injective c n minimal a)
      (cycle_remainder_surjective c (suc. n) (lt_to_book zero. (suc. n) star.) (minimal .fst) a)

def cycle_finite_enumeration (c : Cycles) (n : Nat) (minimal : IsMinimum (PositiveCyclePeriod c) n)
  (a : c .fst .fst .fst) : Equiv (Fin (suc. n)) (c .fst .fst .fst)
  ≔ compose_equiv (Fin (suc. n)) (Remainder (suc. n)) (c .fst .fst .fst)
      (fin_book_below_equiv (suc. n)) (cycle_remainder_equiv c n minimal a)

def cycle_least_period_size (c : Cycles) (n : Nat) (minimal : IsMinimum (PositiveCyclePeriod c) n)
  : Mere (Id Type (c .fst .fst .fst) (Fin (suc. n)))
  ≔ trunc_map native_truncation (c .fst .fst .fst) (Id Type (c .fst .fst .fst) (Fin (suc. n)))
      (a ↦ ua (c .fst .fst .fst) (Fin (suc. n))
        (canonical_inverse_equiv (Fin (suc. n)) (c .fst .fst .fst) (cycle_finite_enumeration c n minimal a))) (c .snd .fst)

def cycle_least_period_finite (c : Cycles) (n : Nat) (minimal : IsMinimum (PositiveCyclePeriod c) n)
  : IsFinite (c .fst .fst .fst)
  ≔ trunc_map native_truncation (Id Type (c .fst .fst .fst) (Fin (suc. n)))
      (Σ Nat (m ↦ Id Type (c .fst .fst .fst) (Fin m))) (p ↦ (suc. n, p)) (cycle_least_period_size c n minimal)

def cycle_least_period_cardinality (c : Cycles) (n : Nat) (minimal : IsMinimum (PositiveCyclePeriod c) n)
  (h : IsFinite (c .fst .fst .fst)) : Id Nat (cardinality (c .fst .fst .fst) h) (suc. n)
  ≔ mere_rec (Id Type (c .fst .fst .fst) (Fin (suc. n)))
      (Id Nat (cardinality (c .fst .fst .fst) h) (suc. n)) (nat_set (cardinality (c .fst .fst .fst) h) (suc. n))
      (cardinality_from_path (c .fst .fst .fst) h (suc. n)) (cycle_least_period_size c n minimal)

def lpo_cycle_size (lpo : LimitedOmniscience) (c : DecidableCycles)
  : Sum (Σ Nat (n ↦ Mere (Id Type (c .fst .fst .fst .fst) (Fin (suc. n)))))
      (Id Order (cycle_order (c .fst)) infinite_order)
  ≔ match lpo_cycle_period_alternative lpo c [
  | inl. m ↦ inl. (m .fst, cycle_least_period_size (c .fst) (m .fst) (m .snd))
  | inr. h ↦ inr. h ]
