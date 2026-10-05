export "170-preimage-transfer"

{` def:RmtoS1 for positive m = suc n.  The fiber over the base is the
   literal Fin m, and the loop is sent to the universe path of the
   successor of the standard finite cycle from cor:id-m-cycle. `}
def power_fiber_set (n : Nat) : SetTypes ≔ (Fin (suc. n), fin_set (suc. n))

def power_fiber_rotation (n : Nat) : Id SetTypes (power_fiber_set n) (power_fiber_set n)
  ≔ subtype_equal Type isSet isset_isprop (power_fiber_set n) (power_fiber_set n)
      (ua (Fin (suc. n)) (Fin (suc. n)) (finite_fin_successor n))

def power_circle_family (C : CircleSignature) (n : Nat) : C .carrier → SetTypes
  ≔ circle_rec C SetTypes (power_fiber_set n, power_fiber_rotation n)

def power_circle_family_beta (C : CircleSignature) (n : Nat)
  : Id (FreeLoop SetTypes) (circle_eval C SetTypes (power_circle_family C n))
      (power_fiber_set n, power_fiber_rotation n)
  ≔ circle_rec_beta C SetTypes (power_fiber_set n, power_fiber_rotation n)

def PowerBundleTotal (C : CircleSignature) (n : Nat) : Type
  ≔ Σ (C .carrier) (z ↦ power_circle_family C n z .fst)

{` The base computation is a propositional path, so the point 0 of
   R_m(base) is transported from the literal Fin m along it. `}
def power_base_trivialization (C : CircleSignature) (n : Nat)
  : Equiv (power_circle_family C n (C .base) .fst) (Fin (suc. n))
  ≔ transport_equiv (power_circle_family C n (C .base) .fst) (Fin (suc. n))
      (power_circle_family_beta C n .fst .fst)

def power_bundle_zero (C : CircleSignature) (n : Nat) : power_circle_family C n (C .base) .fst
  ≔ equiv_inverse_map (power_circle_family C n (C .base) .fst) (Fin (suc. n))
      (power_base_trivialization C n) (inr. star.)

def power_bundle_pointed (C : CircleSignature) (n : Nat) : Pointed
  ≔ (PowerBundleTotal C n, (C .base, power_bundle_zero C n))

{` The m-th power bundle p_m = fst, with pointing path refl base. `}
def power_bundle_map (C : CircleSignature) (n : Nat)
  : BookPointedMap (power_bundle_pointed C n) (circle_pointed C)
  ≔ (t ↦ t .fst, refl (C .base))

def power_bundle_cover (C : CircleSignature) (n : Nat) : Coverings (C .carrier)
  ≔ let c ≔ setfamily_to_covering (C .carrier) (power_circle_family C n) in
    (c .fst .fst, (c .fst .snd, c .snd))

def power_rotation_permutation (n : Nat)
  : Id Permutations (set_loop_permutation (power_fiber_set n, power_fiber_rotation n))
      (power_fiber_set n, finite_fin_successor n)
  ≔ (refl (power_fiber_set n),
      equiv_homotopy (Fin (suc. n)) (Fin (suc. n))
        (transport_equiv (Fin (suc. n)) (Fin (suc. n)) (ua (Fin (suc. n)) (Fin (suc. n)) (finite_fin_successor n)))
        (finite_fin_successor n) (x ↦ refl (finite_fin_successor n .map x)))

{` The monodromy of R_m is the standard finite successor on Fin m. `}
def power_circle_monodromy (C : CircleSignature) (n : Nat)
  : Id Permutations (circle_setfamilies_permutations C .map (power_circle_family C n))
      (power_fiber_set n, finite_fin_successor n)
  ≔ concat Permutations (circle_setfamilies_permutations C .map (power_circle_family C n))
      (set_loop_permutation (power_fiber_set n, power_fiber_rotation n))
      (power_fiber_set n, finite_fin_successor n)
      (refl set_loop_permutation (power_circle_family_beta C n))
      (power_rotation_permutation n)

def power_bundle_connected (C : CircleSignature) (n : Nat) : Connected (PowerBundleTotal C n)
  ≔ equiv_inverse_map (Connected (PowerBundleTotal C n))
      (Cyclic (power_circle_family C n (C .base) .fst)
        (family_monodromy C (z ↦ power_circle_family C n z .fst)))
      (circle_total_connected_cyclic C (z ↦ power_circle_family C n z .fst))
      (transport Permutations cyclic_permutation (power_fiber_set n, finite_fin_successor n)
        (circle_setfamilies_permutations C .map (power_circle_family C n))
        (inverse Permutations (circle_setfamilies_permutations C .map (power_circle_family C n))
          (power_fiber_set n, finite_fin_successor n) (power_circle_monodromy C n))
        (finite_fin_successor_cyclic n))

def power_connected_cover (C : CircleSignature) (n : Nat) : ConnectedCoverings (C .carrier)
  ≔ (power_bundle_cover C n, power_bundle_connected C n)

{` R_m is an m-fold covering: every fiber of p_m merely is Fin m. `}
def power_family_fiber_size (C : CircleSignature) (n : Nat) (z : C .carrier)
  : Mere (Id Type (power_circle_family C n z .fst) (Fin (suc. n)))
  ≔ circle_ind_prop C (z ↦ Mere (Id Type (power_circle_family C n z .fst) (Fin (suc. n))))
      (z ↦ mere_isprop (Id Type (power_circle_family C n z .fst) (Fin (suc. n))))
      (mere (Id Type (power_circle_family C n (C .base) .fst) (Fin (suc. n)))
        (power_circle_family_beta C n .fst .fst)) z

def power_bundle_fiber_size (C : CircleSignature) (n : Nat) (z : C .carrier)
  : Mere (Id Type (BookFiber (PowerBundleTotal C n) (C .carrier) (t ↦ t .fst) z) (Fin (suc. n)))
  ≔ trunc_map native_truncation (Id Type (power_circle_family C n z .fst) (Fin (suc. n)))
      (Id Type (BookFiber (PowerBundleTotal C n) (C .carrier) (t ↦ t .fst) z) (Fin (suc. n)))
      (p ↦ concat Type (BookFiber (PowerBundleTotal C n) (C .carrier) (t ↦ t .fst) z)
        (power_circle_family C n z .fst) (Fin (suc. n))
        (ua (BookFiber (PowerBundleTotal C n) (C .carrier) (t ↦ t .fst) z) (power_circle_family C n z .fst)
          (native_equivalence (BookFiber (PowerBundleTotal C n) (C .carrier) (t ↦ t .fst) z)
            (power_circle_family C n z .fst)
            (book_projection_fiber_equiv (C .carrier) (z ↦ power_circle_family C n z .fst) z))) p)
      (power_family_fiber_size C n z)
