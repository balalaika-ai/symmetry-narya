export "182-cyc-n-universal-property"

def set_loop_transport_power (S : SetTypes) (l : Id SetTypes S S) (k : Nat) (x : S .fst)
  : Id (S .fst) (transport SetTypes ((X ↦ X .fst) : SetTypes → Type) S S (loop_power_nat SetTypes S l k) x)
      (iterate (S .fst) (set_paths_transport_equiv S S .map l .map) k x)
  ≔ let t ≔ set_paths_transport_equiv S S .map l in
    transport_positive_power SetTypes ((X ↦ X .fst) : SetTypes → Type) S l (z ↦ permutation_power (S .fst) t z x)
      (z ↦ inverse (S .fst) (permutation_power (S .fst) t (int_succ z) x)
        (t .map (permutation_power (S .fst) t z x)) (permutation_power_succ (S .fst) t z x)) k

{` Sets with a permutation t such that t^n = id. `}
def CycPermutationData (b : Nat) : Type
  ≔ Σ SetTypes (S ↦ Σ (Equiv (S .fst) (S .fst)) (t ↦ PowerPeriod (S .fst) t (pos. (suc. b))))

def set_loop_order_forward (b : Nat) (S : SetTypes) (l : Id SetTypes S S)
  (w : Id (Id SetTypes S S) (refl S) (loop_power_nat SetTypes S l (suc. b)))
  : PowerPeriod (S .fst) (set_paths_transport_equiv S S .map l) (pos. (suc. b))
  ≔ let R ≔ ((X ↦ X .fst) : SetTypes → Type) in let T ≔ set_paths_transport_equiv S S in
    funext (S .fst) (_ ↦ S .fst) (permutation_power (S .fst) (T .map l) (pos. (suc. b))) (identity (S .fst)) (x ↦ calc
      iterate (S .fst) (T .map l .map) (suc. b) x
      = transport SetTypes R S S (loop_power_nat SetTypes S l (suc. b)) x
        by inverse (S .fst) (transport SetTypes R S S (loop_power_nat SetTypes S l (suc. b)) x)
          (iterate (S .fst) (T .map l .map) (suc. b) x) (set_loop_transport_power S l (suc. b) x)
      = transport SetTypes R S S (refl S) x
        by refl ((m ↦ transport SetTypes R S S m x) : Id SetTypes S S → S .fst)
          (inverse (Id SetTypes S S) (refl S) (loop_power_nat SetTypes S l (suc. b)) w)
      = x by transport_refl SetTypes R S x ∎)

def set_loop_order_backward (b : Nat) (S : SetTypes) (l : Id SetTypes S S)
  (w : PowerPeriod (S .fst) (set_paths_transport_equiv S S .map l) (pos. (suc. b)))
  : Id (Id SetTypes S S) (refl S) (loop_power_nat SetTypes S l (suc. b))
  ≔ let R ≔ ((X ↦ X .fst) : SetTypes → Type) in let T ≔ set_paths_transport_equiv S S in
    equivalence_injective (Id SetTypes S S) (Equiv (S .fst) (S .fst)) T (refl S) (loop_power_nat SetTypes S l (suc. b))
      (equiv_homotopy (S .fst) (S .fst) (T .map (refl S)) (T .map (loop_power_nat SetTypes S l (suc. b))) (x ↦ calc
        T .map (refl S) .map x = x by transport_refl SetTypes R S x
        = iterate (S .fst) (T .map l .map) (suc. b) x
          by inverse (S .fst) (iterate (S .fst) (T .map l .map) (suc. b) x) x
            (happly (S .fst) (_ ↦ S .fst) (permutation_power (S .fst) (T .map l) (pos. (suc. b))) (identity (S .fst)) w x)
        = T .map (loop_power_nat SetTypes S l (suc. b)) .map x by set_loop_transport_power S l (suc. b) x ∎))

def set_loop_order_to (b : Nat) (S : SetTypes)
  (v : Σ (Id SetTypes S S) (l ↦ Id (Id SetTypes S S) (refl S) (loop_power_nat SetTypes S l (suc. b))))
  : Σ (Equiv (S .fst) (S .fst)) (t ↦ PowerPeriod (S .fst) t (pos. (suc. b)))
  ≔ (set_paths_transport_equiv S S .map (v .fst), set_loop_order_forward b S (v .fst) (v .snd))

def set_loop_order_from (b : Nat) (S : SetTypes)
  (v : Σ (Equiv (S .fst) (S .fst)) (t ↦ PowerPeriod (S .fst) t (pos. (suc. b))))
  : Σ (Id SetTypes S S) (l ↦ Id (Id SetTypes S S) (refl S) (loop_power_nat SetTypes S l (suc. b)))
  ≔ let T ≔ set_paths_transport_equiv S S in
    let Tinv ≔ equiv_inverse_map (Id SetTypes S S) (Equiv (S .fst) (S .fst)) T in
    (Tinv (v .fst), set_loop_order_backward b S (Tinv (v .fst))
      (transport (Equiv (S .fst) (S .fst)) (t ↦ PowerPeriod (S .fst) t (pos. (suc. b))) (v .fst) (T .map (Tinv (v .fst)))
        (inverse (Equiv (S .fst) (S .fst)) (T .map (Tinv (v .fst))) (v .fst)
          (equiv_counit (Id SetTypes S S) (Equiv (S .fst) (S .fst)) T (v .fst))) (v .snd)))

{` For a set S, symmetries s : S = S with refl = s^n are permutations t
   with t^n = id; the map sends s to transport along s. `}
def set_loop_order_equiv (b : Nat) (S : SetTypes)
  : Equiv (Σ (Id SetTypes S S) (l ↦ Id (Id SetTypes S S) (refl S) (loop_power_nat SetTypes S l (suc. b))))
      (Σ (Equiv (S .fst) (S .fst)) (t ↦ PowerPeriod (S .fst) t (pos. (suc. b))))
  ≔ let T ≔ set_paths_transport_equiv S S in
    let P ≔ ((l ↦ Id (Id SetTypes S S) (refl S) (loop_power_nat SetTypes S l (suc. b))) : Id SetTypes S S → Type) in
    let Q ≔ ((t ↦ PowerPeriod (S .fst) t (pos. (suc. b))) : Equiv (S .fst) (S .fst) → Type) in
    quasi_inverse_equiv (Σ (Id SetTypes S S) P) (Σ (Equiv (S .fst) (S .fst)) Q)
      (set_loop_order_to b S) (set_loop_order_from b S)
      (v ↦ subtype_equal (Id SetTypes S S) P (l ↦ sets_groupoid S S (refl S) (loop_power_nat SetTypes S l (suc. b)))
        (set_loop_order_from b S (set_loop_order_to b S v)) v
        (equiv_retraction (Id SetTypes S S) (Equiv (S .fst) (S .fst)) T (v .fst)))
      (v ↦ subtype_equal (Equiv (S .fst) (S .fst)) Q (t ↦ power_period_prop (S .fst) (S .snd) t (pos. (suc. b)))
        (set_loop_order_to b S (set_loop_order_from b S v)) v
        (equiv_counit (Id SetTypes S S) (Equiv (S .fst) (S .fst)) T (v .fst)))

{` The first step of the corollary after prop:ump-cycn-into-groupoids:
   families of sets over Cyc_n are sets with a permutation t, t^n = id.
   The map sends S to S(pt_n) and the transport along ap_S(sigma_n). `}
def cyc_set_families_permutations (b : Nat)
  : BookEquiv (CycleComponent (suc. b) → SetTypes) (CycPermutationData b)
  ≔ let C ≔ CycleComponent (suc. b) in
    book_equivalence (C → SetTypes) (CycPermutationData b)
      (compose_equiv (C → SetTypes) (CycSymmetryData b SetTypes) (CycPermutationData b)
        (native_equivalence (C → SetTypes) (CycSymmetryData b SetTypes) (cyc_universal_property b SetTypes sets_groupoid))
        (family_equiv SetTypes
          (S ↦ Σ (Id SetTypes S S) (l ↦ Id (Id SetTypes S S) (refl S) (loop_power_nat SetTypes S l (suc. b))))
          (S ↦ Σ (Equiv (S .fst) (S .fst)) (t ↦ PowerPeriod (S .fst) t (pos. (suc. b))))
          (set_loop_order_equiv b)))
