export "119-one-point-coverings"

def boolean_set : SetTypes ≔ (Bool, bool_set)
def boolean_set_swap : Id SetTypes boolean_set boolean_set
  ≔ subtype_equal Type isSet isset_isprop boolean_set boolean_set bool_swap

def boolean_swap_cyclic : Cyclic Bool bool_not_equiv
  ≔ (mere Bool false., x y ↦ match x, y [
      | false., false. ↦ same_orbit_refl Bool bool_not_equiv false.
      | true., true. ↦ same_orbit_refl Bool bool_not_equiv true.
      | false., true. ↦ mere (OrbitWitness Bool bool_not_equiv false. true.) (pos. (suc. zero.), refl true.)
      | true., false. ↦ mere (OrbitWitness Bool bool_not_equiv true. false.) (pos. (suc. zero.), refl false.) ])

def boolean_swap_permutation : Permutations ≔ (boolean_set, bool_not_equiv)

def set_loop_permutation (d : FreeLoop SetTypes) : Permutations
  ≔ (d .fst, set_paths_transport_equiv (d .fst) (d .fst) .map (d .snd))

def boolean_swap_loop_permutation
  : Id Permutations (set_loop_permutation (boolean_set, boolean_set_swap)) boolean_swap_permutation
  ≔ (refl boolean_set,
      equiv_homotopy Bool Bool (transport_equiv Bool Bool bool_swap) bool_not_equiv (b ↦ refl (bool_not b)))

{` The literal circle recursors into SetTypes used in xca:twoS1coverings. `}
def constant_boolean_circle_family (C : CircleSignature) : C .carrier → SetTypes ≔ z ↦ boolean_set
def identity_boolean_circle_family (C : CircleSignature) : C .carrier → SetTypes
  ≔ circle_rec C SetTypes (boolean_set, refl boolean_set)
def swapping_boolean_circle_family (C : CircleSignature) : C .carrier → SetTypes
  ≔ circle_rec C SetTypes (boolean_set, boolean_set_swap)

def constant_boolean_circle_rec_path (C : CircleSignature)
  : Id (C .carrier → SetTypes) (constant_boolean_circle_family C) (identity_boolean_circle_family C)
  ≔ inverse (C .carrier → SetTypes) (identity_boolean_circle_family C) (constant_boolean_circle_family C)
      (circle_rec_eta C SetTypes (constant_boolean_circle_family C))

def constant_boolean_total_not_connected (C : CircleSignature)
  (h : Connected (Σ (C .carrier) (_ ↦ Bool))) : Empty
  ≔ mere_rec (Id (Σ (C .carrier) (_ ↦ Bool)) (C .base, false.) (C .base, true.)) Empty empty_prop
      (q ↦ bool_encode false. true. (q .snd)) (h .snd (C .base, false.) (C .base, true.))

def swapping_boolean_circle_monodromy (C : CircleSignature)
  : Id Permutations (circle_setfamilies_permutations C .map (swapping_boolean_circle_family C)) boolean_swap_permutation
  ≔ concat Permutations (circle_setfamilies_permutations C .map (swapping_boolean_circle_family C))
      (set_loop_permutation (boolean_set, boolean_set_swap)) boolean_swap_permutation
      (refl set_loop_permutation (circle_rec_beta C SetTypes (boolean_set, boolean_set_swap)))
      boolean_swap_loop_permutation

def swapping_boolean_total_connected (C : CircleSignature)
  : Connected (Σ (C .carrier) (z ↦ swapping_boolean_circle_family C z .fst))
  ≔ equiv_inverse_map
      (Connected (Σ (C .carrier) (z ↦ swapping_boolean_circle_family C z .fst)))
      (Cyclic (swapping_boolean_circle_family C (C .base) .fst)
        (family_monodromy C (z ↦ swapping_boolean_circle_family C z .fst)))
      (circle_total_connected_cyclic C (z ↦ swapping_boolean_circle_family C z .fst))
      (transport Permutations cyclic_permutation boolean_swap_permutation
        (circle_setfamilies_permutations C .map (swapping_boolean_circle_family C))
        (inverse Permutations (circle_setfamilies_permutations C .map (swapping_boolean_circle_family C))
          boolean_swap_permutation (swapping_boolean_circle_monodromy C)) boolean_swap_cyclic)

def constant_boolean_not_swapping (C : CircleSignature)
  (q : Id (C .carrier → SetTypes) (constant_boolean_circle_family C) (swapping_boolean_circle_family C)) : Empty
  ≔ constant_boolean_total_not_connected C
      (transport Type Connected (Σ (C .carrier) (z ↦ swapping_boolean_circle_family C z .fst))
        (Σ (C .carrier) (_ ↦ Bool))
        (inverse Type (Σ (C .carrier) (_ ↦ Bool)) (Σ (C .carrier) (z ↦ swapping_boolean_circle_family C z .fst))
          (refl ((F ↦ Σ (C .carrier) (z ↦ F z .fst)) : (C .carrier → SetTypes) → Type) q))
        (swapping_boolean_total_connected C))
