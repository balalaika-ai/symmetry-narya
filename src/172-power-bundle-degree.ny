export "171-power-bundles"

{` The monodromy cycle of R_m is the standard cycle on the literal Fin m. `}
def power_cover_cycle_path (C : CircleSignature) (n : Nat)
  : Id Cycles (circle_connected_coverings_cycles C .map (power_connected_cover C n)) (finite_fin_cycle n)
  ≔ subtype_equal Permutations cyclic_permutation (p ↦ cyclic_prop (p .fst .fst) (p .snd))
      (circle_connected_coverings_cycles C .map (power_connected_cover C n)) (finite_fin_cycle n)
      (concat Permutations (circle_coverings_permutations C .map (power_bundle_cover C n))
        (circle_setfamilies_permutations C .map (power_circle_family C n))
        (power_fiber_set n, finite_fin_successor n)
        (refl (circle_setfamilies_permutations C .map)
          (setfamilies_coverings_beta (C .carrier) (power_circle_family C n)))
        (power_circle_monodromy C n))

{` The standard cycles on Fin m and on the remainders below m agree. `}
def fin_remainder_cycle_path (n : Nat) : Id Cycles (finite_fin_cycle n) (finite_standard_cycle n)
  ≔ let e ≔ fin_book_below_equiv (suc. n) in
    equiv_inverse_map (Id Cycles (finite_fin_cycle n) (finite_standard_cycle n))
      (PermutationIsomorphisms (finite_fin_cycle n .fst) (finite_standard_cycle n .fst))
      (cycle_paths_equiv (finite_fin_cycle n) (finite_standard_cycle n))
      (e, x ↦ equiv_counit (Fin (suc. n)) (Remainder (suc. n)) e (modular_successor n (e .map x)))

def power_degree_connected_cover_path (C : CircleSignature) (n : Nat)
  : Id (ConnectedCoverings (C .carrier)) (power_connected_cover C n)
      (circle_degree_connected_cover C (suc. n) (lt_to_book zero. (suc. n) star.))
  ≔ let positive ≔ lt_to_book zero. (suc. n) star. in
    equivalence_injective (ConnectedCoverings (C .carrier)) Cycles
      (native_equivalence (ConnectedCoverings (C .carrier)) Cycles (circle_connected_coverings_cycles C))
      (power_connected_cover C n) (circle_degree_connected_cover C (suc. n) positive)
      (concat Cycles (circle_connected_coverings_cycles C .map (power_connected_cover C n))
        (finite_fin_cycle n) (degree_cover_cycle C (suc. n) positive)
        (power_cover_cycle_path C n)
        (concat Cycles (finite_fin_cycle n) (finite_standard_cycle n) (degree_cover_cycle C (suc. n) positive)
          (fin_remainder_cycle_path n) (degree_cover_standard_cycle C n)))

def power_degree_maps_path (C : CircleSignature) (n : Nat)
  : Id (MapsInto (C .carrier)) (PowerBundleTotal C n, t ↦ t .fst) (C .carrier, circle_degree_map C (suc. n))
  ≔ let q ≔ power_degree_connected_cover_path C n .fst in (q .fst, q .snd .fst)

{` A path of maps into X gives an equivalence of domains and the
   commuting triangle.  The path is a variable here, so no type below
   depends on evaluating a particular (large) path. `}
def maps_path_comparison (X : Type) (u v : MapsInto X) (q : Id (MapsInto X) u v)
  : Σ (BookEquiv (u .fst) (v .fst))
      (e ↦ Id (u .fst → X) (compose (u .fst) (v .fst) X (v .snd) (e .map)) (u .snd))
  ≔ (book_equivalence (u .fst) (v .fst) (transport_equiv (u .fst) (v .fst) (q .fst)),
      funext (u .fst) (_ ↦ X) (compose (u .fst) (v .fst) X (v .snd) (q .fst .trr)) (u .snd)
        (t ↦ inverse X (u .snd t) (v .snd (q .fst .trr t))
          (domain_pathover_evaluate (u .fst) (v .fst) X (q .fst) (u .snd) (v .snd) (q .snd) t)))

{` con:psi-alpha-m: an equivalence psi_m : Tot(R_m) → S¹ together with
   alpha_m : dg_m psi_m = p_m.  They are obtained from the classification
   of connected coverings, not from the explicit clock construction. `}
def PowerDegreeComparison (C : CircleSignature) (n : Nat) : Type
  ≔ Σ (BookEquiv (PowerBundleTotal C n) (C .carrier))
      (psi ↦ Id (PowerBundleTotal C n → C .carrier)
        (compose (PowerBundleTotal C n) (C .carrier) (C .carrier) (circle_degree_map C (suc. n)) (psi .map))
        (t ↦ t .fst))

def power_degree_psi_alpha (C : CircleSignature) (n : Nat) : PowerDegreeComparison C n
  ≔ maps_path_comparison (C .carrier) (PowerBundleTotal C n, t ↦ t .fst)
      (C .carrier, circle_degree_map C (suc. n)) (power_degree_maps_path C n)

{` The explicit equivalence Fin m ≃ dg_m^{-1}(base) after cor:dgm-conncov,
   assembled by xca:preim-eq from any psi_m and alpha_m. `}
def power_comparison_base_fiber_equiv (C : CircleSignature) (n : Nat) (w : PowerDegreeComparison C n)
  : Equiv (Fin (suc. n)) (BookFiber (C .carrier) (C .carrier) (circle_degree_map C (suc. n)) (C .base))
  ≔ let T ≔ PowerBundleTotal C n in
    let R0 ≔ power_circle_family C n (C .base) .fst in
    let psi ≔ native_equivalence T (C .carrier) (w .fst) in
    compose_equiv (Fin (suc. n)) R0
      (BookFiber (C .carrier) (C .carrier) (circle_degree_map C (suc. n)) (C .base))
      (canonical_inverse_equiv R0 (Fin (suc. n)) (power_base_trivialization C n))
      (compose_equiv R0 (BookFiber T (C .carrier) (t ↦ t .fst) (C .base))
        (BookFiber (C .carrier) (C .carrier) (circle_degree_map C (suc. n)) (C .base))
        (native_equivalence R0 (BookFiber T (C .carrier) (t ↦ t .fst) (C .base))
          (book_projection_inclusion_equiv (C .carrier) (z ↦ power_circle_family C n z .fst) (C .base)))
        (native_equivalence (BookFiber T (C .carrier) (t ↦ t .fst) (C .base))
          (BookFiber (C .carrier) (C .carrier) (circle_degree_map C (suc. n)) (C .base))
          (preimage_transfer_equiv T (C .carrier) (C .carrier) (t ↦ t .fst) (circle_degree_map C (suc. n))
            psi (t ↦ inverse (C .carrier) (circle_degree_map C (suc. n) (psi .map t)) (t .fst)
              (happly T (_ ↦ C .carrier)
                (compose T (C .carrier) (C .carrier) (circle_degree_map C (suc. n)) (w .fst .map))
                (t ↦ t .fst) (w .snd) t)) (C .base))))

def power_degree_base_fiber_equiv (C : CircleSignature) (n : Nat)
  : Equiv (Fin (suc. n)) (BookFiber (C .carrier) (C .carrier) (circle_degree_map C (suc. n)) (C .base))
  ≔ power_comparison_base_fiber_equiv C n (power_degree_psi_alpha C n)
