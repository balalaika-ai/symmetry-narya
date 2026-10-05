export "89-finite-cycle-periods"

def cycle_finiteness (c : Cycles) : Type ≔ IsFinite (c .fst .fst .fst)
def cycle_finiteness_prop (c : Cycles) : isProp (cycle_finiteness c)
  ≔ isfinite_prop (c .fst .fst .fst)
def FiniteCycles : Type ≔ Σ Cycles cycle_finiteness

def standard_finite_cycle (n : Nat) : FiniteCycles
  ≔ (finite_standard_cycle n,
      cycle_least_period_finite (finite_standard_cycle n) n (finite_standard_minimum n))

def FiniteCyclesAt (n : Nat) : Type
  ≔ Σ FiniteCycles (c ↦ Mere (Id Cycles (c .fst) (finite_standard_cycle n)))

def finite_cycle_classification_unique (c : FiniteCycles)
  : BookIsContr (Σ Nat (n ↦ Mere (Id Cycles (c .fst) (finite_standard_cycle n))))
  ≔ let classification ≔ finite_cycle_classification (c .fst) (c .snd) in
    (classification, w ↦ subtype_equal Nat
      (n ↦ Mere (Id Cycles (c .fst) (finite_standard_cycle n)))
      (n ↦ mere_isprop (Id Cycles (c .fst) (finite_standard_cycle n))) classification w
      (finite_cycle_index_unique (c .fst) (classification .fst) (w .fst) (classification .snd) (w .snd)))

def finite_cycle_index_component_equiv (n : Nat) (c : FiniteCycles)
  : Equiv (Mere (Id Cycles (c .fst) (finite_standard_cycle n)))
      (Mere (Id FiniteCycles (standard_finite_cycle n) c))
  ≔ native_mere_equiv (Id Cycles (c .fst) (finite_standard_cycle n))
      (Id FiniteCycles (standard_finite_cycle n) c)
      (compose_equiv (Id Cycles (c .fst) (finite_standard_cycle n))
        (Id Cycles (finite_standard_cycle n) (c .fst)) (Id FiniteCycles (standard_finite_cycle n) c)
        (inverse_path_equiv Cycles (c .fst) (finite_standard_cycle n))
        (canonical_inverse_equiv (Id FiniteCycles (standard_finite_cycle n) c)
          (Id Cycles (finite_standard_cycle n) (c .fst))
          (subtype_path_equiv Cycles cycle_finiteness cycle_finiteness_prop (standard_finite_cycle n) c)))

def finite_cycles_at_component (n : Nat)
  : Equiv (FiniteCyclesAt n) (NativeComponent FiniteCycles (standard_finite_cycle n))
  ≔ family_equiv FiniteCycles (c ↦ Mere (Id Cycles (c .fst) (finite_standard_cycle n)))
      (c ↦ Mere (Id FiniteCycles (standard_finite_cycle n) c)) (finite_cycle_index_component_equiv n)

def finite_cycles_at_full_component (n : Nat)
  : Equiv (FiniteCyclesAt n) (NativeComponent Cycles (finite_standard_cycle n))
  ≔ compose_equiv (FiniteCyclesAt n) (NativeComponent FiniteCycles (standard_finite_cycle n))
      (NativeComponent Cycles (finite_standard_cycle n)) (finite_cycles_at_component n)
      (component_subtype_equiv Cycles cycle_finiteness cycle_finiteness_prop (standard_finite_cycle n))

def finite_cycles_at_total : Equiv (Σ Nat FiniteCyclesAt) FiniteCycles
  ≔ compose_equiv (Σ Nat FiniteCyclesAt)
      (Σ FiniteCycles (c ↦ Σ Nat (n ↦ Mere (Id Cycles (c .fst) (finite_standard_cycle n))))) FiniteCycles
      (sigma_comm Nat FiniteCycles (n c ↦ Mere (Id Cycles (c .fst) (finite_standard_cycle n))))
      (contractible_fiber_projection FiniteCycles
        (c ↦ Σ Nat (n ↦ Mere (Id Cycles (c .fst) (finite_standard_cycle n))))
        (c ↦ native_contraction (Σ Nat (n ↦ Mere (Id Cycles (c .fst) (finite_standard_cycle n))))
          (finite_cycle_classification_unique c)))

def FiniteCycleComponents : Type ≔ Σ Nat (n ↦ NativeComponent Cycles (finite_standard_cycle n))

{` The entire type, including paths and automorphisms in its components,
   decomposes without LPO.  The index n denotes cardinality n+1. `}
def finite_cycle_component_decomposition : Equiv FiniteCycles FiniteCycleComponents
  ≔ compose_equiv FiniteCycles (Σ Nat FiniteCyclesAt) FiniteCycleComponents
      (canonical_inverse_equiv (Σ Nat FiniteCyclesAt) FiniteCycles finite_cycles_at_total)
      (family_equiv Nat FiniteCyclesAt (n ↦ NativeComponent Cycles (finite_standard_cycle n))
        finite_cycles_at_full_component)
