export "224-constructed-circle-checks"
export "211-exponential-fibers"

{` The circle-conditional results of chapter 3, instantiated at the circle
   constructed in modules 220–223 (no postulates). Each constant carries the
   type of the generic theorem with C := constructed_circle written out: a
   definition without a type would store its fully normalized synthesized
   type, which is large and slow to compute for this circle. `}
def S1_book_circle_universal_property (A : Type)
  : BookEquiv (constructed_circle .carrier → A) (FreeLoop A)
  ≔ book_circle_universal_property constructed_circle A

def S1_pointed_circle_universal_property (A : Type) (a : A)
  : Equiv (BookPointedMap (circle_pointed constructed_circle) (A, a)) (Id A a a)
  ≔ pointed_circle_universal_property constructed_circle A a

def S1_circle_dependent_universal_property (P : constructed_circle .carrier → Type)
  : Equiv ((x : constructed_circle .carrier) → P x)
      (CircleBoundary (constructed_circle .carrier) (constructed_circle .base) (constructed_circle .loop) P)
  ≔ circle_dependent_universal_property constructed_circle P

def S1_pointed_circle_loop_type_path (A : Type) (a : A)
  : Id Type (BookPointedMap (circle_pointed constructed_circle) (A, a)) (Id A a a)
  ≔ pointed_circle_loop_type_path constructed_circle A a

def S1_native_circle_connected : Connected (constructed_circle .carrier)
  ≔ native_circle_connected constructed_circle

def S1_constant_boolean_total_not_connected
  (h : Connected (Σ (constructed_circle .carrier) (_ ↦ Bool))) : Empty
  ≔ constant_boolean_total_not_connected constructed_circle h

def S1_swapping_boolean_total_connected
  : Connected (Σ (constructed_circle .carrier) (z ↦ swapping_boolean_circle_family constructed_circle z .fst))
  ≔ swapping_boolean_total_connected constructed_circle

def S1_constant_boolean_not_swapping
  (q : Id (constructed_circle .carrier → SetTypes) (constant_boolean_circle_family constructed_circle)
         (swapping_boolean_circle_family constructed_circle)) : Empty
  ≔ constant_boolean_not_swapping constructed_circle q

def S1_swapping_boolean_cover_not_equivalence
  (h : BookIsEquiv (swapping_boolean_cover constructed_circle .fst) (constructed_circle .carrier)
         (swapping_boolean_cover constructed_circle .snd .fst)) : Empty
  ≔ swapping_boolean_cover_not_equivalence constructed_circle h

def S1_circle_not_finite (h : IsFinite (constructed_circle .carrier)) : Empty
  ≔ circle_not_finite constructed_circle h

def S1_circle_coverings_permutations : Equiv (Coverings (constructed_circle .carrier)) Permutations
  ≔ circle_coverings_permutations constructed_circle

def S1_circle_setfamilies_permutations : Equiv (constructed_circle .carrier → SetTypes) Permutations
  ≔ circle_setfamilies_permutations constructed_circle

def S1_circle_integer_cover : Coverings (constructed_circle .carrier)
  ≔ circle_integer_cover constructed_circle

def S1_circle_exponential_map
  : PointedMap (circle_integer_total_pointed constructed_circle) (circle_pointed constructed_circle)
  ≔ circle_exponential_map constructed_circle

def S1_exponential_fibers_integers (z : constructed_circle .carrier)
  : Mere (Equiv (BookFiber (Σ (constructed_circle .carrier) (circle_integer_family constructed_circle))
                   (constructed_circle .carrier) (t ↦ t .fst) z) Int)
  ≔ exponential_fibers_integers constructed_circle z

def S1_circle_winding_is_transport
  (p : Id (constructed_circle .carrier) (constructed_circle .base) (constructed_circle .base))
  : Id Int (circle_winding constructed_circle p)
      (circle_integer_trivialization constructed_circle
        (code_encode constructed_circle (circle_integer_family constructed_circle)
          (circle_integer_monodromy constructed_circle) (constructed_circle .base) p))
  ≔ circle_winding_is_transport constructed_circle p

def S1_circle_winding_power (n : Int)
  : Id Int
      (circle_winding constructed_circle
        (loop_power (constructed_circle .carrier) (constructed_circle .base) (constructed_circle .loop) n))
      n
  ≔ circle_winding_power constructed_circle n

def S1_circle_integer_trivialization_enumeration (n : Int)
  : Id Int
      (circle_integer_trivialization constructed_circle
        (circle_integer_monodromy constructed_circle .enumeration .map n))
      n
  ≔ circle_integer_trivialization_enumeration constructed_circle n

def S1_code_decode (R : constructed_circle .carrier → Type) (m : CircleCode constructed_circle R)
  : (z : constructed_circle .carrier) → R z → Id (constructed_circle .carrier) (constructed_circle .base) z
  ≔ code_decode constructed_circle R m

def S1_code_decode_beta (R : constructed_circle .carrier → Type) (m : CircleCode constructed_circle R)
  : Id (R (constructed_circle .base)
          → Id (constructed_circle .carrier) (constructed_circle .base) (constructed_circle .base))
      (code_decode constructed_circle R m (constructed_circle .base))
      (code_decode_base constructed_circle R m)
  ≔ code_decode_beta constructed_circle R m

def S1_circle_paths_integer_family_equiv (z : constructed_circle .carrier)
  : Equiv (Id (constructed_circle .carrier) (constructed_circle .base) z)
      (circle_integer_family constructed_circle z)
  ≔ circle_paths_integer_family_equiv constructed_circle z

def S1_circle_integer_total_contractible
  : BookIsContr (Σ (constructed_circle .carrier) (circle_integer_family constructed_circle))
  ≔ circle_integer_total_contractible constructed_circle

def S1_circle_groupoid : isGroupoid (constructed_circle .carrier)
  ≔ circle_groupoid constructed_circle

def S1_circle_integer_loop_equiv
  : BookEquiv Int (Id (constructed_circle .carrier) (constructed_circle .base) (constructed_circle .base))
  ≔ circle_integer_loop_equiv constructed_circle

def S1_circle_integer_cover_universal
  : IsUniversalPointedCover (circle_integer_total_pointed constructed_circle) (circle_pointed constructed_circle)
      (book_circle_exponential_map constructed_circle)
  ≔ circle_integer_cover_universal constructed_circle

def S1_circle_path_cover_universal
  : IsUniversalPointedCover (path_cover_pointed (circle_pointed constructed_circle))
      (circle_pointed constructed_circle)
      (book_pointed_path_projection (circle_pointed constructed_circle))
  ≔ circle_path_cover_universal constructed_circle

def S1_circle_loop_integer_equiv
  : BookEquiv (Id (constructed_circle .carrier) (constructed_circle .base) (constructed_circle .base)) Int
  ≔ circle_loop_integer_equiv constructed_circle

def S1_circle_winding_composition
  (p q : Id (constructed_circle .carrier) (constructed_circle .base) (constructed_circle .base))
  : Id Int
      (circle_winding constructed_circle
        (concat (constructed_circle .carrier) (constructed_circle .base) (constructed_circle .base)
          (constructed_circle .base) p q))
      (int_add (circle_winding constructed_circle p) (circle_winding constructed_circle q))
  ≔ circle_winding_composition constructed_circle p q

def S1_circle_delooping_equiv (A : Type) (connected : Connected A) (a : A)
  (e : Equiv (Id (constructed_circle .carrier) (constructed_circle .base) (constructed_circle .base)) (Id A a a))
  (unit : LoopMapUnit (constructed_circle .carrier) A (constructed_circle .base) a (e .map))
  (composition : LoopMapComposition (constructed_circle .carrier) A (constructed_circle .base) a (e .map))
  : BookEquiv (constructed_circle .carrier) A
  ≔ circle_delooping_equiv constructed_circle A connected a e unit composition

def S1_circle_general_winding_equiv (z : constructed_circle .carrier)
  : Equiv (Id (constructed_circle .carrier) z z) Int
  ≔ circle_general_winding_equiv constructed_circle z

def S1_circle_translation (x : constructed_circle .carrier)
  : BookEquiv (constructed_circle .carrier) (constructed_circle .carrier)
  ≔ circle_translation constructed_circle x

def S1_circle_identity_reflection_different_components
  : Mere (Id (constructed_circle .carrier → constructed_circle .carrier)
            (identity (constructed_circle .carrier)) (circle_reflection constructed_circle))
    → Empty
  ≔ circle_identity_reflection_different_components constructed_circle

def S1_circle_equivalence_two_components (e : Equiv (constructed_circle .carrier) (constructed_circle .carrier))
  : Sum
      (Mere (Id (constructed_circle .carrier → constructed_circle .carrier)
               (identity (constructed_circle .carrier)) (e .map)))
      (Mere (Id (constructed_circle .carrier → constructed_circle .carrier)
               (circle_reflection constructed_circle) (e .map)))
  ≔ circle_equivalence_two_components constructed_circle e

def S1_circle_mapping_coordinates
  : Equiv (constructed_circle .carrier → constructed_circle .carrier) (Σ (constructed_circle .carrier) (_ ↦ Int))
  ≔ circle_mapping_coordinates constructed_circle

def S1_circle_map_component_equiv (f : constructed_circle .carrier → constructed_circle .carrier)
  : Equiv (constructed_circle .carrier)
      (NativeComponent (constructed_circle .carrier → constructed_circle .carrier) f)
  ≔ circle_map_component_equiv constructed_circle f

def S1_circle_symmetries_two_circles
  : Equiv (Equiv (constructed_circle .carrier) (constructed_circle .carrier))
      (Sum (constructed_circle .carrier) (constructed_circle .carrier))
  ≔ circle_symmetries_two_circles constructed_circle

def S1_circle_type_symmetries_two_circles
  : Equiv (Id Type (constructed_circle .carrier) (constructed_circle .carrier))
      (Sum (constructed_circle .carrier) (constructed_circle .carrier))
  ≔ circle_type_symmetries_two_circles constructed_circle

def S1_circle_infinite_cycle_map : constructed_circle .carrier → InfiniteCycles
  ≔ circle_infinite_cycle_map constructed_circle

def S1_circle_infinite_cycles_equiv : BookEquiv (constructed_circle .carrier) InfiniteCycles
  ≔ circle_infinite_cycles_equiv constructed_circle

def S1_circle_components_orbits_equiv (R : constructed_circle .carrier → Type)
  : Equiv (SetTrunc (Σ (constructed_circle .carrier) R))
      (OrbitQuotient (R (constructed_circle .base)) (family_monodromy constructed_circle R))
  ≔ circle_components_orbits_equiv constructed_circle R

def S1_circle_connected_coverings_cycles
  : BookEquiv (ConnectedCoverings (constructed_circle .carrier)) Cycles
  ≔ circle_connected_coverings_cycles constructed_circle

def S1_circle_degree_map (m : Nat) : constructed_circle .carrier → constructed_circle .carrier
  ≔ circle_degree_map constructed_circle m

def S1_degree_winding_image_multiples (m : Nat)
  : Id (Subtypes Int) (degree_winding_image constructed_circle m) (Multiples m)
  ≔ degree_winding_image_multiples constructed_circle m

def S1_power_bundle_cover (n : Nat) : Coverings (constructed_circle .carrier)
  ≔ power_bundle_cover constructed_circle n

def S1_power_circle_monodromy (n : Nat)
  : Id Permutations
      (circle_setfamilies_permutations constructed_circle .map (power_circle_family constructed_circle n))
      (power_fiber_set n, finite_fin_successor n)
  ≔ power_circle_monodromy constructed_circle n

def S1_power_connected_cover (n : Nat) : ConnectedCoverings (constructed_circle .carrier)
  ≔ power_connected_cover constructed_circle n

def S1_power_bundle_fiber_size (n : Nat) (z : constructed_circle .carrier)
  : Mere (Id Type
            (BookFiber (PowerBundleTotal constructed_circle n) (constructed_circle .carrier) (t ↦ t .fst) z)
            (Fin (suc. n)))
  ≔ power_bundle_fiber_size constructed_circle n z

def S1_degree_fiber_size (n : Nat) (b : constructed_circle .carrier)
  : Mere (Id Type
            (BookFiber (constructed_circle .carrier) (constructed_circle .carrier)
              (circle_degree_map constructed_circle (suc. n)) b)
            (Fin (suc. n)))
  ≔ degree_fiber_size constructed_circle n b

def S1_power_degree_psi_alpha (n : Nat) : PowerDegreeComparison constructed_circle n
  ≔ power_degree_psi_alpha constructed_circle n

def S1_power_degree_base_fiber_equiv (n : Nat)
  : Equiv (Fin (suc. n))
      (BookFiber (constructed_circle .carrier) (constructed_circle .carrier)
        (circle_degree_map constructed_circle (suc. n)) (constructed_circle .base))
  ≔ power_degree_base_fiber_equiv constructed_circle n

def S1_circle_degree_connected_cover (m : Nat) (positive : BookLt zero. m)
  : ConnectedCoverings (constructed_circle .carrier)
  ≔ circle_degree_connected_cover constructed_circle m positive

def S1_degree_fiber_cardinality (n : Nat) (b : constructed_circle .carrier)
  (h : IsFinite (BookFiber (constructed_circle .carrier) (constructed_circle .carrier)
                  (circle_degree_map constructed_circle (suc. n)) b))
  : Id Nat
      (cardinality (BookFiber (constructed_circle .carrier) (constructed_circle .carrier)
                     (circle_degree_map constructed_circle (suc. n)) b) h)
      (suc. n)
  ≔ degree_fiber_cardinality constructed_circle n b h

def S1_covering_periods_general_image (c : ConnectedCoverings (constructed_circle .carrier)) (a : c .fst .fst)
  : Id (Subtypes Int) (CyclePeriods (circle_connected_coverings_cycles constructed_circle .map c))
      (general_loop_image constructed_circle (forget_covering (constructed_circle .carrier) (c .fst)) a)
  ≔ covering_periods_general_image constructed_circle c a

def S1_lpo_book_covering_component_sum (lpo : LimitedOmniscience)
  : BookEquiv (ConnectedDecidableCoverings (constructed_circle .carrier))
      (Sum (NativeComponent (Coverings (constructed_circle .carrier)) (circle_universal_cover constructed_circle))
        (Σ Nat (n ↦ NativeComponent (Coverings (constructed_circle .carrier))
          (circle_degree_cover constructed_circle (suc. n) (lt_to_book zero. (suc. n) star.)))))
  ≔ lpo_book_covering_component_sum constructed_circle lpo

def S1_finite_book_covering_components
  : BookEquiv (ConnectedFiniteCoverings (constructed_circle .carrier))
      (FiniteDegreeCoverComponents constructed_circle)
  ≔ finite_book_covering_components constructed_circle

def S1_circle_connected_decidable_coverings_cycles
  : Equiv (ConnectedDecidableCoverings (constructed_circle .carrier)) DecidableCycles
  ≔ circle_connected_decidable_coverings_cycles constructed_circle
