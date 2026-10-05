export "76-finite-cycle-classification"

def finite_infinite_order_distinct (n : Nat) (p : Id Order (finite_cycle_order n) infinite_order) : Empty
  ≔ let q ≔ refl order_periods p in
    let period ≔ transport (Subtypes Int) (H ↦ H (pos. (suc. n)) .fst)
      (CyclePeriods (finite_standard_cycle n)) (CyclePeriods infinite_cycle) q (finite_standard_period n) in
    int_encode (pos. (suc. n)) int_zero (infinite_period_is_zero (pos. (suc. n)) period)

def finite_order_injective (n k : Nat) (p : Id Order (finite_cycle_order n) (finite_cycle_order k)) : Id Nat n k
  ≔ let q ≔ refl order_periods p in
    let forward ≔ transport (Subtypes Int) (H ↦ H (pos. (suc. n)) .fst)
      (CyclePeriods (finite_standard_cycle n)) (CyclePeriods (finite_standard_cycle k)) q (finite_standard_period n) in
    let backward ≔ transport (Subtypes Int) (H ↦ H (pos. (suc. k)) .fst)
      (CyclePeriods (finite_standard_cycle k)) (CyclePeriods (finite_standard_cycle n))
      (inverse (Subtypes Int) (CyclePeriods (finite_standard_cycle n)) (CyclePeriods (finite_standard_cycle k)) q)
      (finite_standard_period k) in
    le_antisym n k (finite_standard_period_lower n k backward) (finite_standard_period_lower k n forward)

def principal_order_injective : PathReflecting Nat Order principal_order
  ≔ n k p ↦ match n, k [
  | zero., zero. ↦ refl zero.
  | zero., suc. k ↦ match finite_infinite_order_distinct k (inverse Order infinite_order (finite_cycle_order k) p) []
  | suc. n, zero. ↦ match finite_infinite_order_distinct n p []
  | suc. n, suc. k ↦ suc. (finite_order_injective n k p) ]

def remainder_decidable_equality (m : Nat) : DecidableEquality (Remainder m)
  ≔ r s ↦ match nat_dec_eq (r .fst) (s .fst) [
  | inl. p ↦ inl. (remainder_equal m r s p)
  | inr. no ↦ inr. (p ↦ no (p .fst)) ]

def principal_cycle_decidable (n : Nat) : DecidableEquality (principal_cycle n .fst .fst .fst)
  ≔ match n [ zero. ↦ int_dec_eq | suc. n ↦ remainder_decidable_equality (suc. n) ]

def principal_decidable_cycle (n : Nat) : DecidableCycles ≔ (principal_cycle n, principal_cycle_decidable n)
def decidable_cycle_order (c : DecidableCycles) : Order ≔ cycle_order (c .fst)

{` The subtype of orders represented by a decidable cycle.  Mere image
   membership retains no chosen representative. `}
def DecidableOrders : Type ≔ Image DecidableCycles Order decidable_cycle_order
def decidable_orders_set : isSet DecidableOrders ≔ image_set DecidableCycles Order decidable_cycle_order order_set

def principal_decidable_order (n : Nat) : DecidableOrders
  ≔ image_factor DecidableCycles Order decidable_cycle_order (principal_decidable_cycle n)

def principal_decidable_order_injective : PathReflecting Nat DecidableOrders principal_decidable_order
  ≔ n k p ↦ principal_order_injective n k (p .fst)

def lpo_cycle_order_classification (lpo : LimitedOmniscience) (c : DecidableCycles)
  : Σ Nat (n ↦ Id Order (decidable_cycle_order c) (principal_order n))
  ≔ let u ≔ lpo_cycle_classification lpo c in
    (u .fst, equiv_inverse_map (Id Order (decidable_cycle_order c) (principal_order (u .fst)))
      (Mere (Id Cycles (c .fst) (principal_cycle (u .fst)))) (set_trunc_paths Cycles (c .fst) (principal_cycle (u .fst))) (u .snd))

def lpo_principal_orders_surjective (lpo : LimitedOmniscience)
  : Surjective Nat DecidableOrders principal_decidable_order
  ≔ d ↦ mere_rec (BookFiber DecidableCycles Order decidable_cycle_order (d .fst))
      (Mere (BookFiber Nat DecidableOrders principal_decidable_order d))
      (mere_isprop (BookFiber Nat DecidableOrders principal_decidable_order d))
      (w ↦ let u ≔ lpo_cycle_order_classification lpo (w .fst) in
        mere (BookFiber Nat DecidableOrders principal_decidable_order d)
          (u .fst, subtype_equal Order (k ↦ Mere (BookFiber DecidableCycles Order decidable_cycle_order k))
            (k ↦ mere_isprop (BookFiber DecidableCycles Order decidable_cycle_order k)) d (principal_decidable_order (u .fst))
            (concat Order (d .fst) (decidable_cycle_order (w .fst)) (principal_order (u .fst)) (w .snd) (u .snd)))) (d .snd)

def lpo_decidable_orders_equiv (lpo : LimitedOmniscience) : Equiv Nat DecidableOrders
  ≔ set_bijection_equiv Nat DecidableOrders decidable_orders_set principal_decidable_order
      principal_decidable_order_injective (lpo_principal_orders_surjective lpo)

def lpo_cycle_order_unique (lpo : LimitedOmniscience) (c : DecidableCycles)
  : BookIsContr (Σ Nat (n ↦ Id Order (decidable_cycle_order c) (principal_order n)))
  ≔ (lpo_cycle_order_classification lpo c,
      u ↦ let v ≔ lpo_cycle_order_classification lpo c in
        subtype_equal Nat (n ↦ Id Order (decidable_cycle_order c) (principal_order n))
          (n ↦ order_set (decidable_cycle_order c) (principal_order n)) v u
          (principal_order_injective (v .fst) (u .fst)
            (concat Order (principal_order (v .fst)) (decidable_cycle_order c) (principal_order (u .fst))
              (inverse Order (decidable_cycle_order c) (principal_order (v .fst)) (v .snd)) (u .snd))))
