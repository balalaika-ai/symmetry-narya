export "183-cyc-n-set-families"

def loop_concat_right_equiv (A : Type) (a z : A) (l : Id A z z) : Equiv (Id A a z) (Id A a z)
  ≔ quasi_inverse_equiv (Id A a z) (Id A a z) (t ↦ concat A a z z t l) (t ↦ concat A a z z t (inverse A z z l))
      (t ↦ calc
        concat A a z z (concat A a z z t l) (inverse A z z l)
        = concat A a z z t (concat A z z z l (inverse A z z l)) by concat_assoc A a z z z t l (inverse A z z l)
        = concat A a z z t (refl z) by refl (concat A a z z t) (concat_inverse_right A z z l)
        = t by concat_p1 A a z t ∎)
      (t ↦ calc
        concat A a z z (concat A a z z t (inverse A z z l)) l
        = concat A a z z t (concat A z z z (inverse A z z l) l) by concat_assoc A a z z z t (inverse A z z l) l
        = concat A a z z t (refl z) by refl (concat A a z z t) (concat_inverse_left A z z l)
        = t by concat_p1 A a z t ∎)

def cyc_loops_right_cyclic (b : Nat)
  : Cyclic (Id (CycleComponent (suc. b)) (principal_component_point (suc. b)) (principal_component_point (suc. b)))
      (loop_concat_right_equiv (CycleComponent (suc. b)) (principal_component_point (suc. b)) (principal_component_point (suc. b))
        (cyc_generator b))
  ≔ let C ≔ CycleComponent (suc. b) in let pt ≔ principal_component_point (suc. b) in
    let L ≔ Id C pt pt in let E ≔ cyc_loop_equiv b in
    let Einv ≔ equiv_inverse_map L (Remainder (suc. b)) E in
    cyclic_transfer (Remainder (suc. b)) L (modular_predecessor_equiv b) (loop_concat_right_equiv C pt pt (cyc_generator b))
      (canonical_inverse_equiv L (Remainder (suc. b)) E)
      (r ↦ inverse_at_known_point L (Remainder (suc. b)) E (concat C pt pt pt (Einv r) (cyc_generator b)) (modular_predecessor b r)
        (concat (Remainder (suc. b)) (E .map (concat C pt pt pt (Einv r) (cyc_generator b)))
          (modular_predecessor b (E .map (Einv r))) (modular_predecessor b r)
          (cyc_loop_right b (Einv r)) (refl (modular_predecessor b) (equiv_counit L (Remainder (suc. b)) E r))))
      (modular_predecessor_cyclic b)

{` The monodromy of a family of sets over Cyc_n: transport along sigma_n. `}
def cyc_family_monodromy (b : Nat) (S : CycleComponent (suc. b) → SetTypes)
  : Equiv (S (principal_component_point (suc. b)) .fst) (S (principal_component_point (suc. b)) .fst)
  ≔ set_paths_transport_equiv (S (principal_component_point (suc. b))) (S (principal_component_point (suc. b)))
      .map (refl S (cyc_generator b))

def cyc_family_loop_action (b : Nat) (S : CycleComponent (suc. b) → SetTypes) (u : S (principal_component_point (suc. b)) .fst)
  : Commutes (Id (CycleComponent (suc. b)) (principal_component_point (suc. b)) (principal_component_point (suc. b)))
      (S (principal_component_point (suc. b)) .fst)
      (loop_concat_right_equiv (CycleComponent (suc. b)) (principal_component_point (suc. b)) (principal_component_point (suc. b))
        (cyc_generator b))
      (cyc_family_monodromy b S)
      (t ↦ transport (CycleComponent (suc. b)) (x ↦ S x .fst) (principal_component_point (suc. b)) (principal_component_point (suc. b)) t u)
  ≔ let C ≔ CycleComponent (suc. b) in let pt ≔ principal_component_point (suc. b) in
    t ↦ transport_concat C (x ↦ S x .fst) pt pt pt t (cyc_generator b) u

def cyc_family_loop_power (b : Nat) (S : CycleComponent (suc. b) → SetTypes) (u : S (principal_component_point (suc. b)) .fst)
  (z : Int)
  : Id (S (principal_component_point (suc. b)) .fst)
      (transport (CycleComponent (suc. b)) (x ↦ S x .fst) (principal_component_point (suc. b)) (principal_component_point (suc. b))
        (permutation_power (Id (CycleComponent (suc. b)) (principal_component_point (suc. b)) (principal_component_point (suc. b)))
          (loop_concat_right_equiv (CycleComponent (suc. b)) (principal_component_point (suc. b)) (principal_component_point (suc. b))
            (cyc_generator b)) z (refl (principal_component_point (suc. b)))) u)
      (permutation_power (S (principal_component_point (suc. b)) .fst) (cyc_family_monodromy b S) z u)
  ≔ let C ≔ CycleComponent (suc. b) in let pt ≔ principal_component_point (suc. b) in
    let R ≔ ((x ↦ S x .fst) : C → Type) in let X ≔ R pt in
    let h ≔ ((t ↦ transport C R pt pt t u) : Id C pt pt → X) in
    concat X (h (permutation_power (Id C pt pt) (loop_concat_right_equiv C pt pt (cyc_generator b)) z (refl pt)))
      (permutation_power X (cyc_family_monodromy b S) z (h (refl pt)))
      (permutation_power X (cyc_family_monodromy b S) z u)
      (permutation_power_intertwine (Id C pt pt) X (loop_concat_right_equiv C pt pt (cyc_generator b)) (cyc_family_monodromy b S)
        h (cyc_family_loop_action b S u) z (refl pt))
      (refl (permutation_power X (cyc_family_monodromy b S) z) (transport_refl C R pt u))

{` Points over pt_n are joined in the total space iff they are in one orbit of the monodromy. `}
def cyc_family_path_orbit (b : Nat) (S : CycleComponent (suc. b) → SetTypes) (u v : S (principal_component_point (suc. b)) .fst)
  (P : Id (Σ (CycleComponent (suc. b)) (x ↦ S x .fst)) (principal_component_point (suc. b), u) (principal_component_point (suc. b), v))
  : SameOrbit (S (principal_component_point (suc. b)) .fst) (cyc_family_monodromy b S) u v
  ≔ let C ≔ CycleComponent (suc. b) in let pt ≔ principal_component_point (suc. b) in
    let R ≔ ((x ↦ S x .fst) : C → Type) in let X ≔ R pt in
    let er ≔ loop_concat_right_equiv C pt pt (cyc_generator b) in
    let moved ≔ pathover_transport_equiv C R pt pt (P .fst) u v .map (P .snd) in
    trunc_map native_truncation (OrbitWitness (Id C pt pt) er (refl pt) (P .fst)) (OrbitWitness X (cyc_family_monodromy b S) u v)
      (w ↦ (w .fst, calc
        v = transport C R pt pt (P .fst) u by inverse X (transport C R pt pt (P .fst) u) v moved
        = transport C R pt pt (permutation_power (Id C pt pt) er (w .fst) (refl pt)) u
          by refl ((m ↦ transport C R pt pt m u) : Id C pt pt → X) (w .snd)
        = permutation_power X (cyc_family_monodromy b S) (w .fst) u by cyc_family_loop_power b S u (w .fst) ∎))
      (cyc_loops_right_cyclic b .snd (refl pt) (P .fst))

def cyc_family_orbit_path (b : Nat) (S : CycleComponent (suc. b) → SetTypes) (u v : S (principal_component_point (suc. b)) .fst)
  (w : OrbitWitness (S (principal_component_point (suc. b)) .fst) (cyc_family_monodromy b S) u v)
  : Id (Σ (CycleComponent (suc. b)) (x ↦ S x .fst)) (principal_component_point (suc. b), u) (principal_component_point (suc. b), v)
  ≔ let C ≔ CycleComponent (suc. b) in let pt ≔ principal_component_point (suc. b) in
    let R ≔ ((x ↦ S x .fst) : C → Type) in let X ≔ R pt in
    let t ≔ permutation_power (Id C pt pt) (loop_concat_right_equiv C pt pt (cyc_generator b)) (w .fst) (refl pt) in
    (t, pathover_of_eq C R pt pt t u v
      (concat X (transport C R pt pt t u) (permutation_power X (cyc_family_monodromy b S) (w .fst) u) v
        (cyc_family_loop_power b S u (w .fst))
        (inverse X v (permutation_power X (cyc_family_monodromy b S) (w .fst) u) (w .snd))))

def cyc_family_base_path (b : Nat) (S : CycleComponent (suc. b) → SetTypes) (e : Σ (CycleComponent (suc. b)) (x ↦ S x .fst))
  (p : Id (CycleComponent (suc. b)) (principal_component_point (suc. b)) (e .fst))
  : Id (Σ (CycleComponent (suc. b)) (x ↦ S x .fst))
      (principal_component_point (suc. b),
        transport (CycleComponent (suc. b)) (x ↦ S x .fst) (e .fst) (principal_component_point (suc. b))
          (inverse (CycleComponent (suc. b)) (principal_component_point (suc. b)) (e .fst) p) (e .snd))
      e
  ≔ let C ≔ CycleComponent (suc. b) in let pt ≔ principal_component_point (suc. b) in
    let R ≔ ((x ↦ S x .fst) : C → Type) in let x ≔ e .fst in
    let q ≔ inverse C pt x p in
    (p, pathover_of_eq C R pt x p (transport C R x pt q (e .snd)) (e .snd) (calc
      transport C R pt x p (transport C R x pt q (e .snd))
      = transport C R pt x (inverse C x pt q) (transport C R x pt q (e .snd))
        by refl ((m ↦ transport C R pt x m (transport C R x pt q (e .snd))) : Id C pt x → R x)
          (inverse (Id C pt x) (inverse C x pt q) p (inverse_inverse C pt x p))
      = e .snd by transport_inverse_roundtrip C R x pt q (e .snd) ∎))

def cyc_family_point_path (b : Nat) (x : CycleComponent (suc. b)) (p : Id Cycles (finite_standard_cycle b) (x .fst))
  : Id (CycleComponent (suc. b)) (principal_component_point (suc. b)) x
  ≔ subtype_equal Cycles (c ↦ Mere (Id Cycles (finite_standard_cycle b) c)) (cyc_component_prop b)
      (principal_component_point (suc. b)) x p

def connected_prop (A : Type) : isProp (Connected A)
  ≔ product_prop (Mere A) ((x y : A) → Mere (Id A x y)) (mere_isprop A)
      (pi_prop A (x ↦ (y : A) → Mere (Id A x y)) (x ↦ pi_prop A (y ↦ Mere (Id A x y)) (y ↦ mere_isprop (Id A x y))))

{` The total space of a family of sets over Cyc_n is connected iff its monodromy is a cycle. `}
def cyc_family_connected_cyclic (b : Nat) (S : CycleComponent (suc. b) → SetTypes)
  : Equiv (Connected (Σ (CycleComponent (suc. b)) (x ↦ S x .fst)))
      (Cyclic (S (principal_component_point (suc. b)) .fst) (cyc_family_monodromy b S))
  ≔ let C ≔ CycleComponent (suc. b) in let pt ≔ principal_component_point (suc. b) in
    let R ≔ ((x ↦ S x .fst) : C → Type) in let X ≔ R pt in let E ≔ Σ C R in
    let t ≔ cyc_family_monodromy b S in
    iff_equiv (Connected E) (Cyclic X t) (connected_prop E) (cyclic_prop X t)
      (h ↦ (mere_rec E (Mere X) (mere_isprop X)
          (e ↦ mere_rec (Id Cycles (finite_standard_cycle b) (e .fst .fst)) (Mere X) (mere_isprop X)
            (p ↦ mere X (transport C R (e .fst) pt (inverse C pt (e .fst) (cyc_family_point_path b (e .fst) p)) (e .snd)))
            (e .fst .snd)) (h .fst),
        u v ↦ mere_rec (Id E (pt, u) (pt, v)) (SameOrbit X t u v) (same_orbit_prop X t u v)
          (cyc_family_path_orbit b S u v) (h .snd (pt, u) (pt, v))))
      (c ↦ (mere_rec X (Mere E) (mere_isprop E) (u ↦ mere E (pt, u)) (c .fst),
        e e' ↦ mere_rec (Id Cycles (finite_standard_cycle b) (e .fst .fst)) (Mere (Id E e e')) (mere_isprop (Id E e e'))
          (p ↦ mere_rec (Id Cycles (finite_standard_cycle b) (e' .fst .fst)) (Mere (Id E e e')) (mere_isprop (Id E e e'))
            (p' ↦ let P ≔ cyc_family_point_path b (e .fst) p in let P' ≔ cyc_family_point_path b (e' .fst) p' in
              let w0 ≔ transport C R (e .fst) pt (inverse C pt (e .fst) P) (e .snd) in
              let w1 ≔ transport C R (e' .fst) pt (inverse C pt (e' .fst) P') (e' .snd) in
              mere_rec (OrbitWitness X t w0 w1) (Mere (Id E e e')) (mere_isprop (Id E e e'))
                (w ↦ mere (Id E e e')
                  (concat E e (pt, w0) e' (inverse E (pt, w0) e (cyc_family_base_path b S e P))
                    (concat E (pt, w0) (pt, w1) e' (cyc_family_orbit_path b S w0 w1 w) (cyc_family_base_path b S e' P'))))
                (c .snd w0 w1))
            (e' .fst .snd))
          (e .fst .snd)))

def cycle_permutation_regroup (b : Nat)
  : Equiv (Σ (CycPermutationData b) (d ↦ Cyclic (d .fst .fst) (d .snd .fst)))
      (Σ Cycles (c ↦ PowerPeriod (c .fst .fst .fst) (c .fst .snd) (pos. (suc. b))))
  ≔ quasi_inverse_equiv (Σ (CycPermutationData b) (d ↦ Cyclic (d .fst .fst) (d .snd .fst)))
      (Σ Cycles (c ↦ PowerPeriod (c .fst .fst .fst) (c .fst .snd) (pos. (suc. b))))
      (v ↦ (((v .fst .fst, v .fst .snd .fst), v .snd), v .fst .snd .snd))
      (v ↦ ((v .fst .fst .fst, (v .fst .fst .snd, v .snd)), v .fst .snd))
      (v ↦ refl v) (v ↦ refl v)

{` The corollary after prop:ump-cycn-into-groupoids: families of sets over
   Cyc_n with connected total space are the cycles (X,t) with t^n = id. `}
def cyc_connected_set_families (b : Nat)
  : BookEquiv (Σ (CycleComponent (suc. b) → SetTypes) (S ↦ Connected (Σ (CycleComponent (suc. b)) (x ↦ S x .fst))))
      (Σ Cycles (c ↦ PowerPeriod (c .fst .fst .fst) (c .fst .snd) (pos. (suc. b))))
  ≔ let C ≔ CycleComponent (suc. b) in
    let F ≔ ((S ↦ Connected (Σ C (x ↦ S x .fst))) : (C → SetTypes) → Type) in
    let G ≔ ((d ↦ Cyclic (d .fst .fst) (d .snd .fst)) : CycPermutationData b → Type) in
    book_equivalence (Σ (C → SetTypes) F) (Σ Cycles (c ↦ PowerPeriod (c .fst .fst .fst) (c .fst .snd) (pos. (suc. b))))
      (compose_equiv (Σ (C → SetTypes) F) (Σ (CycPermutationData b) G)
        (Σ Cycles (c ↦ PowerPeriod (c .fst .fst .fst) (c .fst .snd) (pos. (suc. b))))
        (sigma_equivalences (C → SetTypes) (CycPermutationData b) F G
          (native_equivalence (C → SetTypes) (CycPermutationData b) (cyc_set_families_permutations b))
          (cyc_family_connected_cyclic b))
        (cycle_permutation_regroup b))

{` t^n = id is the book's "the order of (X,t) divides n". `}
def cycle_period_order_divides (b : Nat) (c : Cycles)
  : Equiv (PowerPeriod (c .fst .fst .fst) (c .fst .snd) (pos. (suc. b)))
      (OrderDivides (cycle_order c) (principal_order (suc. b)))
  ≔ iff_equiv (PowerPeriod (c .fst .fst .fst) (c .fst .snd) (pos. (suc. b))) (OrderDivides (cycle_order c) (principal_order (suc. b)))
      (power_period_prop (c .fst .fst .fst) (c .fst .fst .snd) (c .fst .snd) (pos. (suc. b)))
      (order_divides_prop (cycle_order c) (principal_order (suc. b)))
      (p z h ↦ multiple_subgroup_member (CyclePeriods c) (cycle_subgroup_laws c) (suc. b) p z
        (standard_period_multiple b z h))
      (d ↦ d (pos. (suc. b)) (finite_standard_period b))
