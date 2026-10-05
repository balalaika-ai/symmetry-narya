export "59-quotient-presentations"

def family_monodromy (C : CircleSignature) (R : C .carrier → Type)
  : Equiv (R (C .base)) (R (C .base))
  ≔ transport_equiv (R (C .base)) (R (C .base)) (refl R (C .loop))

def family_transport_power (C : CircleSignature) (R : C .carrier → Type) (x : R (C .base)) (n : Int)
  : Id (R (C .base))
      (transport (C .carrier) R (C .base) (C .base) (loop_power (C .carrier) (C .base) (C .loop) n) x)
      (permutation_power (R (C .base)) (family_monodromy C R) n x)
  ≔ transport_loop_power (C .carrier) R (C .base) (C .loop)
      (n ↦ permutation_power (R (C .base)) (family_monodromy C R) n x)
      (n ↦ inverse (R (C .base))
        (permutation_power (R (C .base)) (family_monodromy C R) (int_succ n) x)
        (family_monodromy C R .map (permutation_power (R (C .base)) (family_monodromy C R) n x))
        (permutation_power_succ (R (C .base)) (family_monodromy C R) n x)) n

def family_transport_winding (C : CircleSignature) (R : C .carrier → Type) (x : R (C .base))
  (p : Id (C .carrier) (C .base) (C .base))
  : Id (R (C .base)) (transport (C .carrier) R (C .base) (C .base) p x)
      (permutation_power (R (C .base)) (family_monodromy C R) (circle_winding C p) x)
  ≔ calc
      transport (C .carrier) R (C .base) (C .base) p x
      = transport (C .carrier) R (C .base) (C .base)
          (loop_power (C .carrier) (C .base) (C .loop) (circle_winding C p)) x
        by refl ((q ↦ transport (C .carrier) R (C .base) (C .base) q x)
          : Id (C .carrier) (C .base) (C .base) → R (C .base)) (circle_power_winding C p)
      = permutation_power (R (C .base)) (family_monodromy C R) (circle_winding C p) x
        by family_transport_power C R x (circle_winding C p) ∎

def base_fiber_inclusion (C : CircleSignature) (R : C .carrier → Type) (x : R (C .base))
  : Σ (C .carrier) R ≔ (C .base, x)

def total_path_orbit (C : CircleSignature) (R : C .carrier → Type) (x y : R (C .base))
  (p : Id (Σ (C .carrier) R) (base_fiber_inclusion C R x) (base_fiber_inclusion C R y))
  : OrbitWitness (R (C .base)) (family_monodromy C R) x y
  ≔ (circle_winding C (p .fst), calc
      y = transport (C .carrier) R (C .base) (C .base) (p .fst) x
        by pathover_transport_equiv (C .carrier) R (C .base) (C .base) (p .fst) x y .map (p .snd)
      = permutation_power (R (C .base)) (family_monodromy C R) (circle_winding C (p .fst)) x
        by family_transport_winding C R x (p .fst) ∎)

def orbit_total_path (C : CircleSignature) (R : C .carrier → Type) (x y : R (C .base))
  (w : OrbitWitness (R (C .base)) (family_monodromy C R) x y)
  : Id (Σ (C .carrier) R) (base_fiber_inclusion C R x) (base_fiber_inclusion C R y)
  ≔ let p ≔ loop_power (C .carrier) (C .base) (C .loop) (w .fst) in
    (p, pathover_of_eq (C .carrier) R (C .base) (C .base) p x y (calc
      transport (C .carrier) R (C .base) (C .base) p x
      = permutation_power (R (C .base)) (family_monodromy C R) (w .fst) x by family_transport_power C R x (w .fst)
      = y by w .snd ∎))

def base_fiber_surjective (C : CircleSignature) (R : C .carrier → Type)
  : Surjective (R (C .base)) (Σ (C .carrier) R) (base_fiber_inclusion C R)
  ≔ t ↦ trunc_map native_truncation (Id (C .carrier) (t .fst) (C .base))
      (BookFiber (R (C .base)) (Σ (C .carrier) R) (base_fiber_inclusion C R) t)
      (p ↦ (transport (C .carrier) R (t .fst) (C .base) p (t .snd),
        (p, refl R p .liftr (t .snd))))
      (native_circle_connected C .snd (t .fst) (C .base))

def base_component (C : CircleSignature) (R : C .carrier → Type) (x : R (C .base))
  : SetTrunc (Σ (C .carrier) R) ≔ set_trunc (Σ (C .carrier) R) (base_fiber_inclusion C R x)

def base_component_respects (C : CircleSignature) (R : C .carrier → Type)
  : Respects (R (C .base)) (SetTrunc (Σ (C .carrier) R))
      (orbit_relation (R (C .base)) (family_monodromy C R)) (base_component C R)
  ≔ x y h ↦ quotient_encode (Σ (C .carrier) R) (mere_path_relation (Σ (C .carrier) R))
      (base_fiber_inclusion C R x) (base_fiber_inclusion C R y)
      (trunc_map native_truncation (OrbitWitness (R (C .base)) (family_monodromy C R) x y)
        (Id (Σ (C .carrier) R) (base_fiber_inclusion C R x) (base_fiber_inclusion C R y))
        (orbit_total_path C R x y) h)

def base_component_reflects (C : CircleSignature) (R : C .carrier → Type) (x y : R (C .base))
  (p : Id (SetTrunc (Σ (C .carrier) R)) (base_component C R x) (base_component C R y))
  : SameOrbit (R (C .base)) (family_monodromy C R) x y
  ≔ trunc_map native_truncation
      (Id (Σ (C .carrier) R) (base_fiber_inclusion C R x) (base_fiber_inclusion C R y))
      (OrbitWitness (R (C .base)) (family_monodromy C R) x y) (total_path_orbit C R x y)
      (set_trunc_paths (Σ (C .carrier) R) (base_fiber_inclusion C R x) (base_fiber_inclusion C R y) .map p)

def base_component_surjective (C : CircleSignature) (R : C .carrier → Type)
  : Surjective (R (C .base)) (SetTrunc (Σ (C .carrier) R)) (base_component C R)
  ≔ surjections_compose (R (C .base)) (Σ (C .carrier) R) (SetTrunc (Σ (C .carrier) R))
      (base_fiber_inclusion C R) (set_trunc (Σ (C .carrier) R)) (base_fiber_surjective C R)
      (set_trunc_surjective (Σ (C .carrier) R))

{` con:cycset-connS1cover, for any family and its actual loop transport.
   The only circle assumption is the explicitly supplied signature C. `}
def circle_orbits_components_equiv (C : CircleSignature) (R : C .carrier → Type)
  : Equiv (OrbitQuotient (R (C .base)) (family_monodromy C R)) (SetTrunc (Σ (C .carrier) R))
  ≔ quotient_presentation_equiv (R (C .base)) (SetTrunc (Σ (C .carrier) R))
      (orbit_relation (R (C .base)) (family_monodromy C R)) (set_trunc_set (Σ (C .carrier) R))
      (base_component C R) (base_component_respects C R) (base_component_reflects C R) (base_component_surjective C R)

def circle_orbits_components_beta (C : CircleSignature) (R : C .carrier → Type) (x : R (C .base))
  : Id (SetTrunc (Σ (C .carrier) R))
      (circle_orbits_components_equiv C R .map (quotient_class (R (C .base)) (orbit_relation (R (C .base)) (family_monodromy C R)) x))
      (base_component C R x) ≔ refl (base_component C R x)

def circle_components_orbits_equiv (C : CircleSignature) (R : C .carrier → Type)
  : Equiv (SetTrunc (Σ (C .carrier) R)) (OrbitQuotient (R (C .base)) (family_monodromy C R))
  ≔ canonical_inverse_equiv (OrbitQuotient (R (C .base)) (family_monodromy C R))
      (SetTrunc (Σ (C .carrier) R)) (circle_orbits_components_equiv C R)

def circle_components_orbits_beta (C : CircleSignature) (R : C .carrier → Type) (x : R (C .base))
  : Id (OrbitQuotient (R (C .base)) (family_monodromy C R))
      (circle_components_orbits_equiv C R .map (base_component C R x))
      (quotient_class (R (C .base)) (orbit_relation (R (C .base)) (family_monodromy C R)) x)
  ≔ equiv_retraction (OrbitQuotient (R (C .base)) (family_monodromy C R))
      (SetTrunc (Σ (C .carrier) R)) (circle_orbits_components_equiv C R)
      (quotient_class (R (C .base)) (orbit_relation (R (C .base)) (family_monodromy C R)) x)
