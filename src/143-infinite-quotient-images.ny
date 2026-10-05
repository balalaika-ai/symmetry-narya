export "142-quotient-cycles"
export "164-forgetful-maps"

{` Evaluation of transport in a family of identifications b = G(u). `}
def cycle_path_family_transport_evaluate (D : Type) (G : D → Cycles) (b : Cycles) (u1 u2 : D) (α : Id D u1 u2)
  (γ : Id Cycles b (G u1)) (y : b .fst .fst .fst)
  : Id (G u2 .fst .fst .fst) (cycle_path_evaluate b (G u2) (transport D (u ↦ Id Cycles b (G u)) u1 u2 α γ) y)
      (cycle_path_evaluate (G u1) (G u2) (refl G α) (cycle_path_evaluate b (G u1) γ y))
  ≔ J D u1 (u2 α ↦ Id (G u2 .fst .fst .fst)
        (cycle_path_evaluate b (G u2) (transport D (u ↦ Id Cycles b (G u)) u1 u2 α γ) y)
        (cycle_path_evaluate (G u1) (G u2) (refl G α) (cycle_path_evaluate b (G u1) γ y)))
      (concat (G u1 .fst .fst .fst)
        (cycle_path_evaluate b (G u1) (transport D (u ↦ Id Cycles b (G u)) u1 u1 (refl u1) γ) y)
        (cycle_path_evaluate b (G u1) γ y)
        (cycle_path_evaluate (G u1) (G u1) (refl (G u1)) (cycle_path_evaluate b (G u1) γ y))
        (refl ((p ↦ cycle_path_evaluate b (G u1) p y) : Id Cycles b (G u1) → G u1 .fst .fst .fst)
          (transport_refl D (u ↦ Id Cycles b (G u)) u1 γ))
        (inverse (G u1 .fst .fst .fst)
          (cycle_path_evaluate (G u1) (G u1) (refl (G u1)) (cycle_path_evaluate b (G u1) γ y))
          (cycle_path_evaluate b (G u1) γ y)
          (transport_refl Type (X ↦ X) (G u1 .fst .fst .fst) (cycle_path_evaluate b (G u1) γ y))))
      u2 α

{` The action of X ↦ X/m on paths: [x] ↦ [e(x)]. `}
def quotient_cycle_ap_evaluate (n : Nat) (D : Type) (H : D → Cycles) (u1 u2 : D) (α : Id D u1 u2)
  (x : H u1 .fst .fst .fst)
  : Id (ModQuotient n (H u2 .fst .fst .fst) (H u2 .fst .snd))
      (cycle_path_evaluate (QuotientCycle n (H u1)) (QuotientCycle n (H u2))
        (refl ((u ↦ QuotientCycle n (H u)) : D → Cycles) α)
        (quotient_class (H u1 .fst .fst .fst) (mod_relation n (H u1 .fst .fst .fst) (H u1 .fst .snd)) x))
      (quotient_class (H u2 .fst .fst .fst) (mod_relation n (H u2 .fst .fst .fst) (H u2 .fst .snd))
        (cycle_path_evaluate (H u1) (H u2) (refl H α) x))
  ≔ let X1 ≔ H u1 .fst .fst .fst in let R1 ≔ mod_relation n X1 (H u1 .fst .snd) in
    let Q1 ≔ ModQuotient n X1 (H u1 .fst .snd) in
    J D u1 (u2 α ↦ Id (ModQuotient n (H u2 .fst .fst .fst) (H u2 .fst .snd))
        (cycle_path_evaluate (QuotientCycle n (H u1)) (QuotientCycle n (H u2))
          (refl ((u ↦ QuotientCycle n (H u)) : D → Cycles) α) (quotient_class X1 R1 x))
        (quotient_class (H u2 .fst .fst .fst) (mod_relation n (H u2 .fst .fst .fst) (H u2 .fst .snd))
          (cycle_path_evaluate (H u1) (H u2) (refl H α) x)))
      (concat Q1 (cycle_path_evaluate (QuotientCycle n (H u1)) (QuotientCycle n (H u1)) (refl (QuotientCycle n (H u1)))
          (quotient_class X1 R1 x))
        (quotient_class X1 R1 x)
        (quotient_class X1 R1 (cycle_path_evaluate (H u1) (H u1) (refl (H u1)) x))
        (transport_refl Type (X ↦ X) Q1 (quotient_class X1 R1 x))
        (refl (quotient_class X1 R1) (inverse X1 (cycle_path_evaluate (H u1) (H u1) (refl (H u1)) x) x
          (transport_refl Type (X ↦ X) X1 x))))
      u2 α

{` -/m : Cyc_0 → Set, X ↦ X/m. `}
def infinite_quotient_set (n : Nat) (u : CycleComponent zero.) : SetTypes
  ≔ (ModQuotient n (u .fst .fst .fst .fst) (u .fst .fst .snd),
     quotient_set (u .fst .fst .fst .fst) (mod_relation n (u .fst .fst .fst .fst) (u .fst .fst .snd)))

def infinite_component_divides (n : Nat) (u : CycleComponent zero.)
  : OrderDivides (principal_order (suc. n)) (cycle_order (u .fst))
  ≔ z p ↦ zero_is_period (finite_standard_cycle n) z
      (infinite_period_is_zero z (transport (Subtypes Int) (H ↦ H z .fst) (CyclePeriods (u .fst)) (CyclePeriods infinite_cycle)
        (inverse (Subtypes Int) (CyclePeriods infinite_cycle) (CyclePeriods (u .fst))
          (cycle_paths_imply_periods infinite_cycle (u .fst) (u .snd))) p))

{` The map q : Cyc_0 → Cyc_m of thm:image-Z-to-Cm, (X,t) ↦ (X/m, t̄). `}
def infinite_quotient_cycle (n : Nat) (u : CycleComponent zero.) : CycleComponent (suc. n)
  ≔ (QuotientCycle n (u .fst), quotient_cycle_standard n (u .fst) (infinite_component_divides n u))

{` The map r : Cyc_k → Set to the underlying set. `}
def cycle_component_set (k : Nat) (w : CycleComponent k) : SetTypes ≔ w .fst .fst .fst

def quotient_set_triangle (n : Nat)
  : Id (CycleComponent zero. → SetTypes) (infinite_quotient_set n)
      (compose (CycleComponent zero.) (CycleComponent (suc. n)) SetTypes (cycle_component_set (suc. n))
        (infinite_quotient_cycle n))
  ≔ refl (infinite_quotient_set n)

def cycle_component_set_covering (k : Nat) : IsCovering (CycleComponent k) SetTypes (cycle_component_set k)
  ≔ let two : Nat ≔ suc. (suc. zero.) in
    let B ≔ ((x ↦ Mere (Id Cycles (principal_cycle k) x)) : Cycles → Type) in
    let f1 ≔ projection_truncated two Cycles B
      (x ↦ set_to_hlevel_two (B x) (prop_is_set (B x) (mere_isprop (Id Cycles (principal_cycle k) x)))) in
    let f2 ≔ projection_truncated two Permutations (p ↦ Cyclic (p .fst .fst) (p .snd))
      (p ↦ set_to_hlevel_two (Cyclic (p .fst .fst) (p .snd)) (prop_is_set (Cyclic (p .fst .fst) (p .snd)) (cyclic_prop (p .fst .fst) (p .snd)))) in
    let f3 ≔ projection_truncated two SetTypes (S ↦ Equiv (S .fst) (S .fst))
      (S ↦ set_to_hlevel_two (Equiv (S .fst) (S .fst)) (equivalences_set (S .fst) (S .fst) (S .snd))) in
    let f23 ≔ truncated_maps_compose two Cycles Permutations SetTypes (c ↦ c .fst) (p ↦ p .fst) f2 f3 in
    let h ≔ truncated_maps_compose two (CycleComponent k) Cycles SetTypes (w ↦ w .fst)
      (compose Cycles Permutations SetTypes (p ↦ p .fst) (c ↦ c .fst)) f1 f23 in
    S ↦ hlevel_two_to_set (BookFiber (CycleComponent k) SetTypes (cycle_component_set k) S) (h S)

def infinite_quotient_base_path (n : Nat)
  : Id Cycles (finite_standard_cycle n) (QuotientCycle n infinite_cycle)
  ≔ inverse Cycles (QuotientCycle n infinite_cycle) (finite_standard_cycle n)
      (quotient_cycle_residue_path n infinite_cycle
        (cycle_residue n infinite_cycle (infinite_component_divides n (principal_component_point zero.)) int_zero .fst))

def infinite_quotient_fiber_connected (n : Nat) (b : Cycles) (hb : Mere (Id Cycles (finite_standard_cycle n) b))
  : Connected (BookFiber (CycleComponent zero.) Cycles (u ↦ QuotientCycle n (u .fst)) b)
  ≔ let D ≔ CycleComponent zero. in
    let G ≔ ((u ↦ QuotientCycle n (u .fst)) : D → Cycles) in
    let F ≔ BookFiber D Cycles G b in
    let Bm ≔ ((x ↦ Mere (Id Cycles infinite_cycle x)) : Cycles → Type) in
    (mere_rec (Id Cycles (finite_standard_cycle n) b) (Mere F) (mere_isprop F)
       (β ↦ mere F (principal_component_point zero.,
         concat Cycles b (finite_standard_cycle n) (QuotientCycle n infinite_cycle)
           (inverse Cycles (finite_standard_cycle n) b β) (infinite_quotient_base_path n))) hb,
     v1 v2 ↦
       let d1 ≔ v1 .fst in let d2 ≔ v2 .fst in
       let X1 ≔ d1 .fst .fst .fst .fst in let X2 ≔ d2 .fst .fst .fst .fst in
       let R1 ≔ mod_relation n X1 (d1 .fst .fst .snd) in let R2 ≔ mod_relation n X2 (d2 .fst .fst .snd) in
       let Q1 ≔ ModQuotient n X1 (d1 .fst .fst .snd) in let Q2 ≔ ModQuotient n X2 (d2 .fst .fst .snd) in
       let mp ≔ merely_paths_compose native_truncation Cycles infinite_cycle (d1 .fst) (d2 .fst) (d1 .snd) (d2 .snd) in
       mere_rec (b .fst .fst .fst) (Mere (Id F v1 v2)) (mere_isprop (Id F v1 v2))
         (y0 ↦ mere_rec (BookFiber X1 Q1 (quotient_class X1 R1) (cycle_path_evaluate b (G d1) (v1 .snd) y0))
           (Mere (Id F v1 v2)) (mere_isprop (Id F v1 v2))
           (x0 ↦ mere_rec (BookFiber X2 Q2 (quotient_class X2 R2) (cycle_path_evaluate b (G d2) (v2 .snd) y0))
             (Mere (Id F v1 v2)) (mere_isprop (Id F v1 v2))
             (z ↦
               let pp ≔ cycle_periods_imply_pointed (d1 .fst) (d2 .fst) (cycle_paths_imply_periods (d1 .fst) (d2 .fst) mp)
                 (x0 .fst) (z .fst) .center in
               let α ≔ subtype_equal Cycles Bm (x ↦ mere_isprop (Id Cycles infinite_cycle x)) d1 d2 (pp .fst) in
               let αfst ≔ equiv_counit (Id D d1 d2) (Id Cycles (d1 .fst) (d2 .fst))
                 (subtype_path_equiv Cycles Bm (x ↦ mere_isprop (Id Cycles infinite_cycle x)) d1 d2) (pp .fst) in
               let moved ≔ transport D (u ↦ Id Cycles b (G u)) d1 d2 α (v1 .snd) in
               let E ≔ native_equivalence (Id Cycles b (G d2)) (Q2)
                 (cycle_evaluation_from_component b (G d2) (mere (Id Cycles b (G d2)) (v2 .snd)) y0) in
               let same ≔ equivalence_injective (Id Cycles b (G d2)) Q2 E moved (v2 .snd) (calc
                 cycle_path_evaluate b (G d2) moved y0
                 = cycle_path_evaluate (G d1) (G d2) (refl G α) (cycle_path_evaluate b (G d1) (v1 .snd) y0)
                   by cycle_path_family_transport_evaluate D G b d1 d2 α (v1 .snd) y0
                 = cycle_path_evaluate (G d1) (G d2) (refl G α) (quotient_class X1 R1 (x0 .fst))
                   by refl (cycle_path_evaluate (G d1) (G d2) (refl G α)) (x0 .snd)
                 = quotient_class X2 R2 (cycle_path_evaluate (d1 .fst) (d2 .fst) (refl ((u ↦ u .fst) : D → Cycles) α) (x0 .fst))
                   by quotient_cycle_ap_evaluate n D (u ↦ u .fst) d1 d2 α (x0 .fst)
                 = quotient_class X2 R2 (cycle_path_evaluate (d1 .fst) (d2 .fst) (pp .fst) (x0 .fst))
                   by refl ((p ↦ quotient_class X2 R2 (cycle_path_evaluate (d1 .fst) (d2 .fst) p (x0 .fst)))
                     : Id Cycles (d1 .fst) (d2 .fst) → Q2) αfst
                 = quotient_class X2 R2 (z .fst) by refl (quotient_class X2 R2) (pp .snd)
                 = cycle_path_evaluate b (G d2) (v2 .snd) y0
                   by inverse Q2 (cycle_path_evaluate b (G d2) (v2 .snd) y0) (quotient_class X2 R2 (z .fst)) (z .snd) ∎) in
               mere (Id F v1 v2) (α, pathover_of_eq D (u ↦ Id Cycles b (G u)) d1 d2 α (v1 .snd) (v2 .snd) same))
             (quotient_surjective X2 R2 (cycle_path_evaluate b (G d2) (v2 .snd) y0)))
           (quotient_surjective X1 R1 (cycle_path_evaluate b (G d1) (v1 .snd) y0)))
         (b .snd .fst))

def infinite_quotient_connected_fibers (n : Nat)
  : ConnectedFibers (CycleComponent zero.) (CycleComponent (suc. n)) (infinite_quotient_cycle n)
  ≔ w ↦ connected_equiv (BookFiber (CycleComponent zero.) Cycles (u ↦ QuotientCycle n (u .fst)) (w .fst))
      (BookFiber (CycleComponent zero.) (CycleComponent (suc. n)) (infinite_quotient_cycle n) w)
      (canonical_inverse_equiv (BookFiber (CycleComponent zero.) (CycleComponent (suc. n)) (infinite_quotient_cycle n) w)
        (BookFiber (CycleComponent zero.) Cycles (u ↦ QuotientCycle n (u .fst)) (w .fst))
        (family_equiv (CycleComponent zero.) (u ↦ Id (CycleComponent (suc. n)) w (infinite_quotient_cycle n u))
          (u ↦ Id Cycles (w .fst) (QuotientCycle n (u .fst)))
          (u ↦ subtype_path_equiv Cycles (x ↦ Mere (Id Cycles (finite_standard_cycle n) x))
            (x ↦ mere_isprop (Id Cycles (finite_standard_cycle n) x)) w (infinite_quotient_cycle n u))))
      .map (infinite_quotient_fiber_connected n (w .fst) (w .snd))

def infinite_quotient_zero_connected (n : Nat)
  : ZeroConnectedMap (CycleComponent zero.) (CycleComponent (suc. n)) (infinite_quotient_cycle n)
  ≔ connected_fibers_zero_map (CycleComponent zero.) (CycleComponent (suc. n)) (infinite_quotient_cycle n)
      (infinite_quotient_connected_fibers n)

{` thm:image-Z-to-Cm: (Cyc_m, q, r) is a 0-image factorization of -/m,
   with the triangle holding by reflexivity. `}
def infinite_quotient_factorization (n : Nat)
  : ZeroImageFactorizations (CycleComponent zero.) SetTypes (infinite_quotient_set n)
  ≔ (CycleComponent (suc. n), (infinite_quotient_cycle n, (cycle_component_set (suc. n),
      (quotient_set_triangle n, (infinite_quotient_zero_connected n, cycle_component_set_covering (suc. n))))))

{` By the universal property of the 0-image it is the 0-image factorization. `}
def infinite_quotient_factorization_unique (n : Nat)
  : Id (ZeroImageFactorizations (CycleComponent zero.) SetTypes (infinite_quotient_set n))
      (zero_image_factorization (CycleComponent zero.) SetTypes (infinite_quotient_set n))
      (infinite_quotient_factorization n)
  ≔ let Z ≔ ZeroImageFactorizations (CycleComponent zero.) SetTypes (infinite_quotient_set n) in
    let h ≔ zero_image_universal_property (CycleComponent zero.) SetTypes (infinite_quotient_set n) in
    let canon ≔ zero_image_factorization (CycleComponent zero.) SetTypes (infinite_quotient_set n) in
    concat Z canon (h .center) (infinite_quotient_factorization n)
      (inverse Z (h .center) canon (h .contract canon)) (h .contract (infinite_quotient_factorization n))
