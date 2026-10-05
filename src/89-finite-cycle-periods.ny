export "88-circle-translations"

def int_difference_zero_equal (x y : Int) (p : Id Int (int_sub x y) int_zero) : Id Int x y
  ≔ calc
      x = int_add (int_sub x y) y by int_sub_add x y
      = int_add int_zero y by refl ((z ↦ int_add z y) : Int → Int) p
      = y by int_add_zero_left y ∎

def nonzero_cycle_period_positive (c : Cycles) (z : Int)
  (nonzero : Id Int z int_zero → Empty) (period : CyclePeriods c z .fst)
  : Σ Nat (PositiveCyclePeriod c)
  ≔ match z [
  | pos. zero. ↦ absurd (Σ Nat (PositiveCyclePeriod c)) (nonzero (refl int_zero))
  | pos. (suc. n) ↦ (n, period)
  | neg. n ↦ (n, power_period_neg (c .fst .fst .fst) (c .fst .snd) (neg. n) period) ]

{` N+1 iterates in an N-element carrier collide.  Their distinct indices
   give a nonzero integer period, whose sign can be made positive. `}
def enumerated_cycle_positive_period (c : Cycles) (N : Nat)
  (enumeration : Equiv (c .fst .fst .fst) (Fin N)) (a : c .fst .fst .fst)
  : Σ Nat (PositiveCyclePeriod c)
  ≔ let orbit : Fin (suc. N) → c .fst .fst .fst
      ≔ i ↦ permutation_power (c .fst .fst .fst) (c .fst .snd) (pos. (fin_index (suc. N) i)) a in
    let collision ≔ fin_pigeonhole N (i ↦ enumeration .map (orbit i)) in
    let x : Int ≔ pos. (fin_index (suc. N) (collision .left)) in
    let y : Int ≔ pos. (fin_index (suc. N) (collision .right)) in
    nonzero_cycle_period_positive c (int_sub x y)
      (p ↦ collision .distinct (fin_index_injective (suc. N) (collision .left) (collision .right)
        (refl int_magnitude (int_difference_zero_equal x y p))))
      (cycle_period_from_point (c .fst .fst .fst) (c .fst .fst .snd) (c .fst .snd) (c .snd) a (int_sub x y)
        (power_equality_difference (c .fst .fst .fst) (c .fst .snd) x y a
          (equivalence_injective (c .fst .fst .fst) (Fin N) enumeration
            (orbit (collision .left)) (orbit (collision .right)) (collision .same))))

{` Both the finite enumeration and the point remain truncated.  Elimination
   uses only the proposition that some positive period exists. `}
def finite_cycle_positive_period (c : Cycles) (finite : IsFinite (c .fst .fst .fst))
  : Mere (Σ Nat (PositiveCyclePeriod c))
  ≔ mere_rec (Σ Nat (N ↦ Id Type (c .fst .fst .fst) (Fin N)))
      (Mere (Σ Nat (PositiveCyclePeriod c))) (mere_isprop (Σ Nat (PositiveCyclePeriod c)))
      (w ↦ trunc_map native_truncation (c .fst .fst .fst) (Σ Nat (PositiveCyclePeriod c))
        (enumerated_cycle_positive_period c (w .fst)
          (id_to_equiv (c .fst .fst .fst) (Fin (w .fst)) (w .snd))) (c .snd .fst)) finite

def finite_cycle_minimum (c : Cycles) (finite : IsFinite (c .fst .fst .fst))
  : Σ Nat (IsMinimum (PositiveCyclePeriod c))
  ≔ least_number (PositiveCyclePeriod c) (n ↦ CyclePeriods c (pos. (suc. n)) .snd)
      (n ↦ cycle_period_decidable c (finite_decidable_equality (c .fst .fst .fst) finite) (pos. (suc. n)))
      (finite_cycle_positive_period c finite)

def finite_cycle_classification (c : Cycles) (finite : IsFinite (c .fst .fst .fst))
  : Σ Nat (n ↦ Mere (Id Cycles c (finite_standard_cycle n)))
  ≔ let minimum ≔ finite_cycle_minimum c finite in
    (minimum .fst, finite_cycle_component c (minimum .fst) (minimum .snd))

def finite_cycle_cardinality (c : Cycles) (finite : IsFinite (c .fst .fst .fst))
  : Id Nat (cardinality (c .fst .fst .fst) finite) (suc. (finite_cycle_minimum c finite .fst))
  ≔ cycle_least_period_cardinality c (finite_cycle_minimum c finite .fst)
      (finite_cycle_minimum c finite .snd) finite

def finite_cycle_index_unique (c : Cycles) (n k : Nat)
  (p : Mere (Id Cycles c (finite_standard_cycle n)))
  (q : Mere (Id Cycles c (finite_standard_cycle k))) : Id Nat n k
  ≔ finite_order_injective n k (concat Order (finite_cycle_order n) (cycle_order c) (finite_cycle_order k)
      (inverse Order (cycle_order c) (finite_cycle_order n)
        (equiv_inverse_map (Id Order (cycle_order c) (finite_cycle_order n))
          (Mere (Id Cycles c (finite_standard_cycle n))) (set_trunc_paths Cycles c (finite_standard_cycle n)) p))
      (equiv_inverse_map (Id Order (cycle_order c) (finite_cycle_order k))
        (Mere (Id Cycles c (finite_standard_cycle k))) (set_trunc_paths Cycles c (finite_standard_cycle k)) q))
