export "78-cycle-component-decomposition"

def CoveringDecidable (B : Type) (c : Coverings B) : Type
  ≔ (b : B) → DecidableEquality (BookFiber (c .fst) B (c .snd .fst) b)

def covering_decidable_prop (B : Type) (c : Coverings B) : isProp (CoveringDecidable B c)
  ≔ pi_prop B (b ↦ DecidableEquality (BookFiber (c .fst) B (c .snd .fst) b))
      (b ↦ decidable_equality_prop (BookFiber (c .fst) B (c .snd .fst) b) (c .snd .snd b))

def ConnectedDecidableCoverings (B : Type) : Type
  ≔ Σ (ConnectedCoverings B) (c ↦ CoveringDecidable B (c .fst))

def connected_covering_decidable_at (B : Type) (connected : Connected B) (base : B) (c : Coverings B)
  : Equiv (CoveringDecidable B c) (DecidableEquality (BookFiber (c .fst) B (c .snd .fst) base))
  ≔ iff_equiv (CoveringDecidable B c) (DecidableEquality (BookFiber (c .fst) B (c .snd .fst) base))
      (covering_decidable_prop B c)
      (decidable_equality_prop (BookFiber (c .fst) B (c .snd .fst) base) (c .snd .snd base))
      (h ↦ h base)
      (connected_based_elim native_truncation B connected base
        (b ↦ DecidableEquality (BookFiber (c .fst) B (c .snd .fst) b))
        (b ↦ decidable_equality_prop (BookFiber (c .fst) B (c .snd .fst) b) (c .snd .snd b)))

def circle_connected_decidable_coverings_cycles (C : CircleSignature)
  : Equiv (ConnectedDecidableCoverings (C .carrier)) DecidableCycles
  ≔ propositional_subtype_equiv (ConnectedCoverings (C .carrier)) Cycles
      (c ↦ CoveringDecidable (C .carrier) (c .fst)) cycle_decidability
      (c ↦ covering_decidable_prop (C .carrier) (c .fst)) cycle_decidability_prop
      (native_equivalence (ConnectedCoverings (C .carrier)) Cycles (circle_connected_coverings_cycles C))
      (c ↦ connected_covering_decidable_at (C .carrier) (native_circle_connected C) (C .base) (c .fst))

def component_equiv (A B : Type) (e : Equiv A B) (a : A)
  : Equiv (NativeComponent A a) (NativeComponent B (e .map a))
  ≔ propositional_subtype_equiv A B (x ↦ Mere (Id A a x)) (y ↦ Mere (Id B (e .map a) y))
      (x ↦ mere_isprop (Id A a x)) (y ↦ mere_isprop (Id B (e .map a) y)) e
      (x ↦ native_mere_equiv (Id A a x) (Id B (e .map a) (e .map x)) (equivalence_on_paths A B e a x))

def component_equiv_at_target (A B : Type) (e : Equiv A B) (b : B)
  : Equiv (NativeComponent A (equiv_inverse_map A B e b)) (NativeComponent B b)
  ≔ compose_equiv (NativeComponent A (equiv_inverse_map A B e b))
      (NativeComponent B (e .map (equiv_inverse_map A B e b))) (NativeComponent B b)
      (component_equiv A B e (equiv_inverse_map A B e b))
      (id_to_equiv (NativeComponent B (e .map (equiv_inverse_map A B e b))) (NativeComponent B b)
        (refl (NativeComponent B) (equiv_counit A B e b)))

{` These coverings are constructed from their monodromy.  Modules 83-84
   compare them with the degree-m maps and the path covering. `}
def principal_connected_covering (C : CircleSignature) (n : Nat) : ConnectedCoverings (C .carrier)
  ≔ equiv_inverse_map (ConnectedCoverings (C .carrier)) Cycles
      (native_equivalence (ConnectedCoverings (C .carrier)) Cycles (circle_connected_coverings_cycles C)) (principal_cycle n)

def principal_covering_monodromy (C : CircleSignature) (n : Nat)
  : Id Cycles (circle_connected_coverings_cycles C .map (principal_connected_covering C n)) (principal_cycle n)
  ≔ equiv_counit (ConnectedCoverings (C .carrier)) Cycles
      (native_equivalence (ConnectedCoverings (C .carrier)) Cycles (circle_connected_coverings_cycles C)) (principal_cycle n)

def principal_covering_component_equiv (C : CircleSignature) (n : Nat)
  : Equiv (NativeComponent (Coverings (C .carrier)) (principal_connected_covering C n .fst))
      (NativeComponent Cycles (principal_cycle n))
  ≔ compose_equiv (NativeComponent (Coverings (C .carrier)) (principal_connected_covering C n .fst))
      (NativeComponent (ConnectedCoverings (C .carrier)) (principal_connected_covering C n))
      (NativeComponent Cycles (principal_cycle n))
      (canonical_inverse_equiv
        (NativeComponent (ConnectedCoverings (C .carrier)) (principal_connected_covering C n))
        (NativeComponent (Coverings (C .carrier)) (principal_connected_covering C n .fst))
        (component_subtype_equiv (Coverings (C .carrier)) (c ↦ Connected (c .fst))
          (c ↦ connected_isprop (c .fst)) (principal_connected_covering C n)))
      (component_equiv_at_target (ConnectedCoverings (C .carrier)) Cycles
        (native_equivalence (ConnectedCoverings (C .carrier)) Cycles (circle_connected_coverings_cycles C)) (principal_cycle n))

def PrincipalCoveringComponents (C : CircleSignature) : Type
  ≔ Σ Nat (n ↦ NativeComponent (Coverings (C .carrier)) (principal_connected_covering C n .fst))

def lpo_connected_covering_components (C : CircleSignature) (lpo : LimitedOmniscience)
  : Equiv (ConnectedDecidableCoverings (C .carrier)) (PrincipalCoveringComponents C)
  ≔ compose_equiv (ConnectedDecidableCoverings (C .carrier)) PrincipalCycleComponents (PrincipalCoveringComponents C)
      (compose_equiv (ConnectedDecidableCoverings (C .carrier)) DecidableCycles PrincipalCycleComponents
        (circle_connected_decidable_coverings_cycles C) (lpo_cycle_component_decomposition lpo))
      (family_equiv Nat (n ↦ NativeComponent Cycles (principal_cycle n))
        (n ↦ NativeComponent (Coverings (C .carrier)) (principal_connected_covering C n .fst))
        (n ↦ canonical_inverse_equiv
          (NativeComponent (Coverings (C .carrier)) (principal_connected_covering C n .fst))
          (NativeComponent Cycles (principal_cycle n)) (principal_covering_component_equiv C n)))

def lpo_connected_covering_component_sum (C : CircleSignature) (lpo : LimitedOmniscience)
  : Equiv (ConnectedDecidableCoverings (C .carrier))
      (Sum (NativeComponent (Coverings (C .carrier)) (principal_connected_covering C zero. .fst))
        (Σ Nat (n ↦ NativeComponent (Coverings (C .carrier)) (principal_connected_covering C (suc. n) .fst))))
  ≔ compose_equiv (ConnectedDecidableCoverings (C .carrier)) (PrincipalCoveringComponents C)
      (Sum (NativeComponent (Coverings (C .carrier)) (principal_connected_covering C zero. .fst))
        (Σ Nat (n ↦ NativeComponent (Coverings (C .carrier)) (principal_connected_covering C (suc. n) .fst))))
      (lpo_connected_covering_components C lpo)
      (sigma_nat_zero_successor (n ↦ NativeComponent (Coverings (C .carrier)) (principal_connected_covering C n .fst)))
