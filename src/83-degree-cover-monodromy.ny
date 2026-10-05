export "82-covering-loop-images"

def cycle_path_from_periods (c d : Cycles) (h : Id (Subtypes Int) (CyclePeriods c) (CyclePeriods d))
  (x : c .fst .fst .fst) (y : d .fst .fst .fst) : Id Cycles c d
  ≔ cycle_evaluation_from_periods c d h x .equiv y .center .fst

def degree_cover_cycle (C : CircleSignature) (m : Nat) (positive : BookLt zero. m) : Cycles
  ≔ circle_connected_coverings_cycles C .map (circle_degree_connected_cover C m positive)

def degree_cover_base_point (C : CircleSignature) (m : Nat) (positive : BookLt zero. m)
  : degree_cover_cycle C m positive .fst .fst .fst
  ≔ (C .base, inverse (C .carrier) (circle_degree_map C m (C .base)) (C .base) (circle_degree_boundary C m .fst))

def degree_cover_periods (C : CircleSignature) (m : Nat) (positive : BookLt zero. m)
  : Id (Subtypes Int) (CyclePeriods (degree_cover_cycle C m positive)) (Multiples m)
  ≔ concat (Subtypes Int) (CyclePeriods (degree_cover_cycle C m positive)) (degree_winding_image C m) (Multiples m)
      (covering_periods_based_image C (circle_degree_connected_cover C m positive)
        (C .base) (circle_degree_boundary C m .fst))
      (degree_winding_image_multiples C m)

def degree_cover_standard_cycle (C : CircleSignature) (n : Nat)
  : Id Cycles (finite_standard_cycle n) (degree_cover_cycle C (suc. n) (lt_to_book zero. (suc. n) star.))
  ≔ cycle_path_from_periods (finite_standard_cycle n) (degree_cover_cycle C (suc. n) (lt_to_book zero. (suc. n) star.))
      (concat (Subtypes Int) (CyclePeriods (finite_standard_cycle n)) (Multiples (suc. n))
        (CyclePeriods (degree_cover_cycle C (suc. n) (lt_to_book zero. (suc. n) star.)))
        (finite_standard_periods n)
        (inverse (Subtypes Int) (CyclePeriods (degree_cover_cycle C (suc. n) (lt_to_book zero. (suc. n) star.)))
          (Multiples (suc. n)) (degree_cover_periods C (suc. n) (lt_to_book zero. (suc. n) star.))))
      (remainder_at n zero. star.) (degree_cover_base_point C (suc. n) (lt_to_book zero. (suc. n) star.))

def principal_degree_connected_cover_path (C : CircleSignature) (n : Nat)
  : Id (ConnectedCoverings (C .carrier)) (principal_connected_covering C (suc. n))
      (circle_degree_connected_cover C (suc. n) (lt_to_book zero. (suc. n) star.))
  ≔ equivalence_injective (ConnectedCoverings (C .carrier)) Cycles
      (native_equivalence (ConnectedCoverings (C .carrier)) Cycles (circle_connected_coverings_cycles C))
      (principal_connected_covering C (suc. n)) (circle_degree_connected_cover C (suc. n) (lt_to_book zero. (suc. n) star.))
      (concat Cycles (circle_connected_coverings_cycles C .map (principal_connected_covering C (suc. n)))
        (finite_standard_cycle n) (degree_cover_cycle C (suc. n) (lt_to_book zero. (suc. n) star.))
        (principal_covering_monodromy C (suc. n)) (degree_cover_standard_cycle C n))

def principal_degree_cover_path (C : CircleSignature) (n : Nat)
  : Id (Coverings (C .carrier)) (principal_connected_covering C (suc. n) .fst)
      (circle_degree_cover C (suc. n) (lt_to_book zero. (suc. n) star.))
  ≔ principal_degree_connected_cover_path C n .fst

def degree_base_fiber_enumeration (C : CircleSignature) (n : Nat)
  : Equiv (Fin (suc. n))
      (BookFiber (C .carrier) (C .carrier) (circle_degree_map C (suc. n)) (C .base))
  ≔ compose_equiv (Fin (suc. n)) (Remainder (suc. n))
      (BookFiber (C .carrier) (C .carrier) (circle_degree_map C (suc. n)) (C .base))
      (fin_book_below_equiv (suc. n))
      (cycle_paths_equiv (finite_standard_cycle n) (degree_cover_cycle C (suc. n) (lt_to_book zero. (suc. n) star.))
        .map (degree_cover_standard_cycle C n) .fst)

def degree_fiber_size (C : CircleSignature) (n : Nat) (b : C .carrier)
  : Mere (Id Type (BookFiber (C .carrier) (C .carrier) (circle_degree_map C (suc. n)) b) (Fin (suc. n)))
  ≔ connected_based_elim native_truncation (C .carrier) (native_circle_connected C) (C .base)
      (b ↦ Mere (Id Type (BookFiber (C .carrier) (C .carrier) (circle_degree_map C (suc. n)) b) (Fin (suc. n))))
      (b ↦ mere_isprop (Id Type (BookFiber (C .carrier) (C .carrier) (circle_degree_map C (suc. n)) b) (Fin (suc. n))))
      (mere (Id Type (BookFiber (C .carrier) (C .carrier) (circle_degree_map C (suc. n)) (C .base)) (Fin (suc. n)))
        (ua (BookFiber (C .carrier) (C .carrier) (circle_degree_map C (suc. n)) (C .base)) (Fin (suc. n))
          (canonical_inverse_equiv (Fin (suc. n))
            (BookFiber (C .carrier) (C .carrier) (circle_degree_map C (suc. n)) (C .base)) (degree_base_fiber_enumeration C n)))) b

def degree_fiber_finite (C : CircleSignature) (n : Nat) (b : C .carrier)
  : IsFinite (BookFiber (C .carrier) (C .carrier) (circle_degree_map C (suc. n)) b)
  ≔ trunc_map native_truncation
      (Id Type (BookFiber (C .carrier) (C .carrier) (circle_degree_map C (suc. n)) b) (Fin (suc. n)))
      (Σ Nat (k ↦ Id Type (BookFiber (C .carrier) (C .carrier) (circle_degree_map C (suc. n)) b) (Fin k)))
      (p ↦ (suc. n, p)) (degree_fiber_size C n b)

def degree_fiber_cardinality (C : CircleSignature) (n : Nat) (b : C .carrier)
  (h : IsFinite (BookFiber (C .carrier) (C .carrier) (circle_degree_map C (suc. n)) b))
  : Id Nat (cardinality (BookFiber (C .carrier) (C .carrier) (circle_degree_map C (suc. n)) b) h) (suc. n)
  ≔ mere_rec (Id Type (BookFiber (C .carrier) (C .carrier) (circle_degree_map C (suc. n)) b) (Fin (suc. n)))
      (Id Nat (cardinality (BookFiber (C .carrier) (C .carrier) (circle_degree_map C (suc. n)) b) h) (suc. n))
      (nat_set (cardinality (BookFiber (C .carrier) (C .carrier) (circle_degree_map C (suc. n)) b) h) (suc. n))
      (cardinality_from_path (BookFiber (C .carrier) (C .carrier) (circle_degree_map C (suc. n)) b) h (suc. n))
      (degree_fiber_size C n b)

def degree_cover_decidable (C : CircleSignature) (n : Nat)
  : CoveringDecidable (C .carrier) (circle_degree_cover C (suc. n) (lt_to_book zero. (suc. n) star.))
  ≔ b ↦ finite_decidable_equality (BookFiber (C .carrier) (C .carrier) (circle_degree_map C (suc. n)) b)
      (degree_fiber_finite C n b)
