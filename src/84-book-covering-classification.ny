export "83-degree-cover-monodromy"

def contractible_connected (A : Type) (h : BookIsContr A) : Connected A
  ≔ (mere A (h .center), x y ↦ mere (Id A x y)
      (contractible_prop A (native_contraction A h) x y))

def contractible_based_loop_zero (C : CircleSignature) (t : MapsInto (C .carrier))
  (h : BookIsContr (t .fst)) (a : t .fst) (base : Id (C .carrier) (t .snd a) (C .base)) (p : Id (t .fst) a a)
  : Id Int (based_loop_winding C t a base p) int_zero
  ≔ concat Int (based_loop_winding C t a base p) (based_loop_winding C t a base (refl a)) int_zero
      (refl (based_loop_winding C t a base)
        (prop_is_set (t .fst) (contractible_prop (t .fst) (native_contraction (t .fst) h)) a a p (refl a)))
      (based_loop_winding_refl C t a base)

def contractible_based_loop_image (C : CircleSignature) (t : MapsInto (C .carrier))
  (h : BookIsContr (t .fst)) (a : t .fst) (base : Id (C .carrier) (t .snd a) (C .base))
  : Id (Subtypes Int) (based_loop_image C t a base) ZeroPeriods
  ≔ funext Int (_ ↦ PropTypes) (based_loop_image C t a base) ZeroPeriods
      (z ↦ proposition_extensionality (based_loop_image C t a base z) (ZeroPeriods z)
        (mere_rec (BookFiber (Id (t .fst) a a) Int (based_loop_winding C t a base) z)
          (Id Int z int_zero) (int_set z int_zero)
          (w ↦ concat Int z (based_loop_winding C t a base (w .fst)) int_zero (w .snd)
            (contractible_based_loop_zero C t h a base (w .fst))))
        (p ↦ mere (BookFiber (Id (t .fst) a a) Int (based_loop_winding C t a base) z)
          (refl a, concat Int z int_zero (based_loop_winding C t a base (refl a)) p
            (inverse Int (based_loop_winding C t a base (refl a)) int_zero (based_loop_winding_refl C t a base)))))

def circle_universal_cover (C : CircleSignature) : Coverings (C .carrier)
  ≔ path_cover (C .carrier) (circle_groupoid C) (C .base)

def circle_universal_connected_cover (C : CircleSignature) : ConnectedCoverings (C .carrier)
  ≔ (circle_universal_cover C,
      contractible_connected (circle_universal_cover C .fst) (path_cover_contractible (C .carrier) (circle_groupoid C) (C .base)))

def universal_cover_cycle (C : CircleSignature) : Cycles
  ≔ circle_connected_coverings_cycles C .map (circle_universal_connected_cover C)

def universal_cover_base_point (C : CircleSignature) : universal_cover_cycle C .fst .fst .fst
  ≔ ((C .base, refl (C .base)), refl (C .base))

def universal_cover_periods (C : CircleSignature)
  : Id (Subtypes Int) (CyclePeriods (universal_cover_cycle C)) ZeroPeriods
  ≔ concat (Subtypes Int) (CyclePeriods (universal_cover_cycle C))
      (based_loop_image C (forget_covering (C .carrier) (circle_universal_cover C)) (C .base, refl (C .base)) (refl (C .base)))
      ZeroPeriods
      (covering_periods_based_image C (circle_universal_connected_cover C) (C .base, refl (C .base)) (refl (C .base)))
      (contractible_based_loop_image C (forget_covering (C .carrier) (circle_universal_cover C))
        (path_cover_contractible (C .carrier) (circle_groupoid C) (C .base)) (C .base, refl (C .base)) (refl (C .base)))

def universal_cover_infinite_cycle (C : CircleSignature) : Id Cycles infinite_cycle (universal_cover_cycle C)
  ≔ cycle_path_from_periods infinite_cycle (universal_cover_cycle C)
      (concat (Subtypes Int) (CyclePeriods infinite_cycle) ZeroPeriods (CyclePeriods (universal_cover_cycle C))
        infinite_cycle_periods
        (inverse (Subtypes Int) (CyclePeriods (universal_cover_cycle C)) ZeroPeriods (universal_cover_periods C)))
      int_zero (universal_cover_base_point C)

def principal_universal_connected_cover_path (C : CircleSignature)
  : Id (ConnectedCoverings (C .carrier)) (principal_connected_covering C zero.) (circle_universal_connected_cover C)
  ≔ equivalence_injective (ConnectedCoverings (C .carrier)) Cycles
      (native_equivalence (ConnectedCoverings (C .carrier)) Cycles (circle_connected_coverings_cycles C))
      (principal_connected_covering C zero.) (circle_universal_connected_cover C)
      (concat Cycles (circle_connected_coverings_cycles C .map (principal_connected_covering C zero.))
        infinite_cycle (universal_cover_cycle C) (principal_covering_monodromy C zero.) (universal_cover_infinite_cycle C))

def principal_universal_cover_path (C : CircleSignature)
  : Id (Coverings (C .carrier)) (principal_connected_covering C zero. .fst) (circle_universal_cover C)
  ≔ principal_universal_connected_cover_path C .fst

def book_standard_cover (C : CircleSignature) (n : Nat) : Coverings (C .carrier)
  ≔ match n [ zero. ↦ circle_universal_cover C | suc. n ↦ circle_degree_cover C (suc. n) (lt_to_book zero. (suc. n) star.) ]

def principal_book_standard_cover_path (C : CircleSignature) (n : Nat)
  : Id (Coverings (C .carrier)) (principal_connected_covering C n .fst) (book_standard_cover C n)
  ≔ match n [ zero. ↦ principal_universal_cover_path C | suc. n ↦ principal_degree_cover_path C n ]

def BookStandardCoverComponents (C : CircleSignature) : Type
  ≔ Σ Nat (n ↦ NativeComponent (Coverings (C .carrier)) (book_standard_cover C n))

def lpo_book_covering_components (C : CircleSignature) (lpo : LimitedOmniscience)
  : Equiv (ConnectedDecidableCoverings (C .carrier)) (BookStandardCoverComponents C)
  ≔ compose_equiv (ConnectedDecidableCoverings (C .carrier)) (PrincipalCoveringComponents C) (BookStandardCoverComponents C)
      (lpo_connected_covering_components C lpo)
      (family_equiv Nat (n ↦ NativeComponent (Coverings (C .carrier)) (principal_connected_covering C n .fst))
        (n ↦ NativeComponent (Coverings (C .carrier)) (book_standard_cover C n))
        (n ↦ id_to_equiv (NativeComponent (Coverings (C .carrier)) (principal_connected_covering C n .fst))
          (NativeComponent (Coverings (C .carrier)) (book_standard_cover C n))
          (refl (NativeComponent (Coverings (C .carrier))) (principal_book_standard_cover_path C n))))

{` lem:componentsofcoversofS1. The representatives here are the actual path
   covering and actual degree maps, not only reconstructions from monodromy.
   Both the circle signature and LPO remain explicit parameters. `}
def lpo_book_covering_component_sum (C : CircleSignature) (lpo : LimitedOmniscience)
  : BookEquiv (ConnectedDecidableCoverings (C .carrier))
      (Sum (NativeComponent (Coverings (C .carrier)) (circle_universal_cover C))
        (Σ Nat (n ↦ NativeComponent (Coverings (C .carrier))
          (circle_degree_cover C (suc. n) (lt_to_book zero. (suc. n) star.)))))
  ≔ book_equivalence (ConnectedDecidableCoverings (C .carrier))
      (Sum (NativeComponent (Coverings (C .carrier)) (circle_universal_cover C))
        (Σ Nat (n ↦ NativeComponent (Coverings (C .carrier))
          (circle_degree_cover C (suc. n) (lt_to_book zero. (suc. n) star.)))))
      (compose_equiv (ConnectedDecidableCoverings (C .carrier)) (BookStandardCoverComponents C)
        (Sum (NativeComponent (Coverings (C .carrier)) (circle_universal_cover C))
          (Σ Nat (n ↦ NativeComponent (Coverings (C .carrier))
            (circle_degree_cover C (suc. n) (lt_to_book zero. (suc. n) star.)))))
        (lpo_book_covering_components C lpo)
        (sigma_nat_zero_successor (n ↦ NativeComponent (Coverings (C .carrier)) (book_standard_cover C n))))
