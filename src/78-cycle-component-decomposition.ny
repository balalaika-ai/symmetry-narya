export "77-decidable-orders"

def cycle_decidability (c : Cycles) : Type ≔ DecidableEquality (c .fst .fst .fst)
def cycle_decidability_prop (c : Cycles) : isProp (cycle_decidability c)
  ≔ decidable_equality_prop (c .fst .fst .fst) (c .fst .fst .snd)

def DecidableCyclesAt (n : Nat) : Type
  ≔ Σ DecidableCycles (c ↦ Id Order (decidable_cycle_order c) (principal_order n))

def cycle_index_component_equiv (n : Nat) (c : DecidableCycles)
  : Equiv (Id Order (decidable_cycle_order c) (principal_order n))
      (Mere (Id DecidableCycles (principal_decidable_cycle n) c))
  ≔ compose_equiv (Id Order (decidable_cycle_order c) (principal_order n))
      (Mere (Id Cycles (principal_cycle n) (c .fst)))
      (Mere (Id DecidableCycles (principal_decidable_cycle n) c))
      (compose_equiv (Id Order (decidable_cycle_order c) (principal_order n))
        (Id Order (principal_order n) (decidable_cycle_order c))
        (Mere (Id Cycles (principal_cycle n) (c .fst)))
        (inverse_path_equiv Order (decidable_cycle_order c) (principal_order n))
        (set_trunc_paths Cycles (principal_cycle n) (c .fst)))
      (native_mere_equiv (Id Cycles (principal_cycle n) (c .fst))
        (Id DecidableCycles (principal_decidable_cycle n) c)
        (canonical_inverse_equiv (Id DecidableCycles (principal_decidable_cycle n) c)
          (Id Cycles (principal_cycle n) (c .fst))
          (subtype_path_equiv Cycles cycle_decidability cycle_decidability_prop (principal_decidable_cycle n) c)))

def decidable_cycles_at_component (n : Nat)
  : Equiv (DecidableCyclesAt n) (NativeComponent DecidableCycles (principal_decidable_cycle n))
  ≔ family_equiv DecidableCycles (c ↦ Id Order (decidable_cycle_order c) (principal_order n))
      (c ↦ Mere (Id DecidableCycles (principal_decidable_cycle n) c)) (cycle_index_component_equiv n)

def decidable_cycles_at_full_component (n : Nat)
  : Equiv (DecidableCyclesAt n) (NativeComponent Cycles (principal_cycle n))
  ≔ compose_equiv (DecidableCyclesAt n) (NativeComponent DecidableCycles (principal_decidable_cycle n))
      (NativeComponent Cycles (principal_cycle n)) (decidable_cycles_at_component n)
      (component_subtype_equiv Cycles cycle_decidability cycle_decidability_prop (principal_decidable_cycle n))

def lpo_decidable_cycles_at_total (lpo : LimitedOmniscience)
  : Equiv (Σ Nat DecidableCyclesAt) DecidableCycles
  ≔ compose_equiv (Σ Nat DecidableCyclesAt)
      (Σ DecidableCycles (c ↦ Σ Nat (n ↦ Id Order (decidable_cycle_order c) (principal_order n)))) DecidableCycles
      (sigma_comm Nat DecidableCycles (n c ↦ Id Order (decidable_cycle_order c) (principal_order n)))
      (contractible_fiber_projection DecidableCycles
        (c ↦ Σ Nat (n ↦ Id Order (decidable_cycle_order c) (principal_order n)))
        (c ↦ native_contraction (Σ Nat (n ↦ Id Order (decidable_cycle_order c) (principal_order n)))
          (lpo_cycle_order_unique lpo c)))

def PrincipalCycleComponents : Type ≔ Σ Nat (n ↦ NativeComponent Cycles (principal_cycle n))

{` This is an equivalence of the whole types, retaining automorphism paths
   inside every component, not only a bijection of their sets of components. `}
def lpo_cycle_component_decomposition (lpo : LimitedOmniscience)
  : Equiv DecidableCycles PrincipalCycleComponents
  ≔ compose_equiv DecidableCycles (Σ Nat DecidableCyclesAt) PrincipalCycleComponents
      (canonical_inverse_equiv (Σ Nat DecidableCyclesAt) DecidableCycles (lpo_decidable_cycles_at_total lpo))
      (family_equiv Nat DecidableCyclesAt (n ↦ NativeComponent Cycles (principal_cycle n)) decidable_cycles_at_full_component)

def principal_cycle_components_connected (n : Nat) : Connected (NativeComponent Cycles (principal_cycle n))
  ≔ native_component_connected Cycles (principal_cycle n)

def sigma_nat_split_at (P : Nat → Type) (n : Nat) (p : P n)
  : Sum (P zero.) (Σ Nat (n ↦ P (suc. n)))
  ≔ match n [ zero. ↦ inl. p | suc. n ↦ inr. (n, p) ]

def sigma_nat_join (P : Nat → Type) : Sum (P zero.) (Σ Nat (n ↦ P (suc. n))) → Σ Nat P
  ≔ [ inl. z ↦ (zero., z) | inr. t ↦ (suc. (t .fst), t .snd) ]

def sigma_nat_join_split (P : Nat → Type) (n : Nat) (p : P n)
  : Id (Σ Nat P) (sigma_nat_join P (sigma_nat_split_at P n p)) (n, p)
  ≔ match n [ zero. ↦ refl (zero., p) | suc. n ↦ refl (suc. n, p) ]

def sigma_nat_zero_successor (P : Nat → Type)
  : Equiv (Σ Nat P) (Sum (P zero.) (Σ Nat (n ↦ P (suc. n))))
  ≔ quasi_inverse_equiv (Σ Nat P) (Sum (P zero.) (Σ Nat (n ↦ P (suc. n))))
      (t ↦ sigma_nat_split_at P (t .fst) (t .snd)) (sigma_nat_join P)
      (t ↦ sigma_nat_join_split P (t .fst) (t .snd))
      [ inl. z ↦ refl (inl. z) | inr. t ↦ refl (inr. t) ]

def lpo_cycle_component_sum (lpo : LimitedOmniscience)
  : Equiv DecidableCycles
      (Sum (NativeComponent Cycles infinite_cycle) (Σ Nat (n ↦ NativeComponent Cycles (finite_standard_cycle n))))
  ≔ compose_equiv DecidableCycles PrincipalCycleComponents
      (Sum (NativeComponent Cycles infinite_cycle) (Σ Nat (n ↦ NativeComponent Cycles (finite_standard_cycle n))))
      (lpo_cycle_component_decomposition lpo) (sigma_nat_zero_successor (n ↦ NativeComponent Cycles (principal_cycle n)))
