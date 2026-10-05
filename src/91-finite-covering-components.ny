export "90-finite-cycle-components"

{` Finiteness means that every fiber is finite; the total space is not
   required to be a finite set. `}
def CoveringFinite (B : Type) (c : Coverings B) : Type
  ≔ (b : B) → IsFinite (BookFiber (c .fst) B (c .snd .fst) b)

def covering_finite_prop (B : Type) (c : Coverings B) : isProp (CoveringFinite B c)
  ≔ pi_prop B (b ↦ IsFinite (BookFiber (c .fst) B (c .snd .fst) b))
      (b ↦ isfinite_prop (BookFiber (c .fst) B (c .snd .fst) b))

def ConnectedFiniteCoverings (B : Type) : Type
  ≔ Σ (ConnectedCoverings B) (c ↦ CoveringFinite B (c .fst))

def connected_covering_finite_at (B : Type) (connected : Connected B) (base : B) (c : Coverings B)
  : Equiv (CoveringFinite B c) (IsFinite (BookFiber (c .fst) B (c .snd .fst) base))
  ≔ iff_equiv (CoveringFinite B c) (IsFinite (BookFiber (c .fst) B (c .snd .fst) base))
      (covering_finite_prop B c) (isfinite_prop (BookFiber (c .fst) B (c .snd .fst) base))
      (h ↦ h base)
      (connected_based_elim native_truncation B connected base
        (b ↦ IsFinite (BookFiber (c .fst) B (c .snd .fst) b))
        (b ↦ isfinite_prop (BookFiber (c .fst) B (c .snd .fst) b)))

def circle_connected_finite_coverings_cycles (C : CircleSignature)
  : Equiv (ConnectedFiniteCoverings (C .carrier)) FiniteCycles
  ≔ propositional_subtype_equiv (ConnectedCoverings (C .carrier)) Cycles
      (c ↦ CoveringFinite (C .carrier) (c .fst)) cycle_finiteness
      (c ↦ covering_finite_prop (C .carrier) (c .fst)) cycle_finiteness_prop
      (native_equivalence (ConnectedCoverings (C .carrier)) Cycles (circle_connected_coverings_cycles C))
      (c ↦ connected_covering_finite_at (C .carrier) (native_circle_connected C) (C .base) (c .fst))

def finite_covering_index (C : CircleSignature) (c : ConnectedFiniteCoverings (C .carrier)) : Nat
  ≔ finite_cycle_minimum (circle_connected_coverings_cycles C .map (c .fst)) (c .snd (C .base)) .fst

def finite_covering_index_cardinality (C : CircleSignature) (c : ConnectedFiniteCoverings (C .carrier))
  (b : C .carrier)
  : Id Nat (cardinality (BookFiber (c .fst .fst .fst) (C .carrier) (c .fst .fst .snd .fst) b) (c .snd b))
      (suc. (finite_covering_index C c))
  ≔ connected_based_elim native_truncation (C .carrier) (native_circle_connected C) (C .base)
      (b ↦ Id Nat (cardinality (BookFiber (c .fst .fst .fst) (C .carrier) (c .fst .fst .snd .fst) b) (c .snd b))
        (suc. (finite_covering_index C c)))
      (b ↦ nat_set (cardinality (BookFiber (c .fst .fst .fst) (C .carrier) (c .fst .fst .snd .fst) b) (c .snd b))
        (suc. (finite_covering_index C c)))
      (finite_cycle_cardinality (circle_connected_coverings_cycles C .map (c .fst)) (c .snd (C .base))) b

def finite_connected_covering_classification (C : CircleSignature) (c : ConnectedFiniteCoverings (C .carrier))
  : Mere (Id (Coverings (C .carrier)) (c .fst .fst)
      (circle_degree_cover C (suc. (finite_covering_index C c))
        (lt_to_book zero. (suc. (finite_covering_index C c)) star.)))
  ≔ trunc_map native_truncation
      (Id Cycles (circle_connected_coverings_cycles C .map (c .fst))
        (finite_standard_cycle (finite_covering_index C c)))
      (Id (Coverings (C .carrier)) (c .fst .fst)
        (circle_degree_cover C (suc. (finite_covering_index C c))
          (lt_to_book zero. (suc. (finite_covering_index C c)) star.)))
      (p ↦ equivalence_injective (ConnectedCoverings (C .carrier)) Cycles
        (native_equivalence (ConnectedCoverings (C .carrier)) Cycles (circle_connected_coverings_cycles C))
        (c .fst) (circle_degree_connected_cover C (suc. (finite_covering_index C c))
          (lt_to_book zero. (suc. (finite_covering_index C c)) star.))
        (concat Cycles (circle_connected_coverings_cycles C .map (c .fst))
          (finite_standard_cycle (finite_covering_index C c))
          (degree_cover_cycle C (suc. (finite_covering_index C c))
            (lt_to_book zero. (suc. (finite_covering_index C c)) star.))
          p (degree_cover_standard_cycle C (finite_covering_index C c))) .fst)
      (finite_cycle_component (circle_connected_coverings_cycles C .map (c .fst)) (finite_covering_index C c)
        (finite_cycle_minimum (circle_connected_coverings_cycles C .map (c .fst)) (c .snd (C .base)) .snd))

def FinitePrincipalCoveringComponents (C : CircleSignature) : Type
  ≔ Σ Nat (n ↦ NativeComponent (Coverings (C .carrier)) (principal_connected_covering C (suc. n) .fst))

def finite_connected_covering_components (C : CircleSignature)
  : Equiv (ConnectedFiniteCoverings (C .carrier)) (FinitePrincipalCoveringComponents C)
  ≔ compose_equiv (ConnectedFiniteCoverings (C .carrier)) FiniteCycleComponents (FinitePrincipalCoveringComponents C)
      (compose_equiv (ConnectedFiniteCoverings (C .carrier)) FiniteCycles FiniteCycleComponents
        (circle_connected_finite_coverings_cycles C) finite_cycle_component_decomposition)
      (family_equiv Nat (n ↦ NativeComponent Cycles (finite_standard_cycle n))
        (n ↦ NativeComponent (Coverings (C .carrier)) (principal_connected_covering C (suc. n) .fst))
        (n ↦ canonical_inverse_equiv
          (NativeComponent (Coverings (C .carrier)) (principal_connected_covering C (suc. n) .fst))
          (NativeComponent Cycles (finite_standard_cycle n)) (principal_covering_component_equiv C (suc. n))))

def FiniteDegreeCoverComponents (C : CircleSignature) : Type
  ≔ Σ Nat (n ↦ NativeComponent (Coverings (C .carrier))
      (circle_degree_cover C (suc. n) (lt_to_book zero. (suc. n) star.)))

{` The representatives are the book's actual degree maps of positive degree.
   The circle signature is explicit; no classical principle is supplied. `}
def finite_book_covering_components (C : CircleSignature)
  : BookEquiv (ConnectedFiniteCoverings (C .carrier)) (FiniteDegreeCoverComponents C)
  ≔ book_equivalence (ConnectedFiniteCoverings (C .carrier)) (FiniteDegreeCoverComponents C)
      (compose_equiv (ConnectedFiniteCoverings (C .carrier)) (FinitePrincipalCoveringComponents C)
        (FiniteDegreeCoverComponents C) (finite_connected_covering_components C)
        (family_equiv Nat (n ↦ NativeComponent (Coverings (C .carrier)) (principal_connected_covering C (suc. n) .fst))
          (n ↦ NativeComponent (Coverings (C .carrier))
            (circle_degree_cover C (suc. n) (lt_to_book zero. (suc. n) star.)))
          (n ↦ id_to_equiv (NativeComponent (Coverings (C .carrier)) (principal_connected_covering C (suc. n) .fst))
            (NativeComponent (Coverings (C .carrier))
              (circle_degree_cover C (suc. n) (lt_to_book zero. (suc. n) star.)))
            (refl (NativeComponent (Coverings (C .carrier))) (principal_degree_cover_path C n)))))
