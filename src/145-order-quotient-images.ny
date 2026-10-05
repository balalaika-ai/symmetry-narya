export "144-order-lattice"

def int_mul_cancel_pos (n : Nat) (q r : Int)
  (p : Id Int (int_mul q (pos. (suc. n))) (int_mul r (pos. (suc. n)))) : Id Int q r
  ≔ let z ≔ int_mul q (pos. (suc. n)) in
    let positive ≔ lt_to_book zero. (suc. n) star. in
    let D ≔ IntegerDivisionResult z (suc. n) in
    let u : D ≔ ((q, zero.), (positive, refl z)) in
    let v : D ≔ ((r, zero.), (positive, p)) in
    let contr ≔ integer_euclidean_division_unique z (suc. n) positive in
    refl ((w ↦ w .fst .fst) : D → Int)
      (concat D u (contr .center) v (inverse D (contr .center) u (contr .contract u)) (contr .contract v))

def scaled_member_cancel (n : Nat) (H : Subtypes Int) (q : Int)
  (s : ScaledSubtype (suc. n) H (int_mul q (pos. (suc. n))) .fst) : H q .fst
  ≔ mere_rec (ScaledWitness (suc. n) H (int_mul q (pos. (suc. n)))) (H q .fst) (H q .snd)
      (v ↦ transport Int (x ↦ H x .fst) (v .fst .fst) q
        (inverse Int q (v .fst .fst) (int_mul_cancel_pos n q (v .fst .fst) (v .fst .snd))) (v .snd)) s

{` The order md: the root on orders. `}
def order_root (n : Nat) : Order → Order
  ≔ set_trunc_rec Cycles Order order_set (c ↦ cycle_order (cycle_root n c))

def order_root_periods (n : Nat) (d : Order)
  : Id (Subtypes Int) (order_periods (order_root n d)) (ScaledSubtype (suc. n) (order_periods d))
  ≔ set_trunc_induction Cycles
      (d ↦ Id (Subtypes Int) (order_periods (order_root n d)) (ScaledSubtype (suc. n) (order_periods d)))
      (d ↦ prop_is_set (Id (Subtypes Int) (order_periods (order_root n d)) (ScaledSubtype (suc. n) (order_periods d)))
        (subtypes_set Int (order_periods (order_root n d)) (ScaledSubtype (suc. n) (order_periods d))))
      (c ↦ root_cycle_periods n c) d

def root_order_divides (n : Nat) (d : Order) : OrderDivides (principal_order (suc. n)) (order_root n d)
  ≔ z p ↦ mere_rec (ScaledWitness (suc. n) (order_periods d) z) (order_periods (principal_order (suc. n)) z .fst)
      (order_periods (principal_order (suc. n)) z .snd)
      (v ↦ standard_multiple_period n z (v .fst))
      (transport (Subtypes Int) (H ↦ H z .fst) (order_periods (order_root n d)) (ScaledSubtype (suc. n) (order_periods d))
        (order_root_periods n d) p)

{` The restriction cdg_m : Cyc_d → Cyc_md. `}
def cycle_root_of_order (n : Nat) (d : Order) (v : CyclesOfOrder d) : CyclesOfOrder (order_root n d)
  ≔ (cycle_root n (v .fst), refl (order_root n) (v .snd))

{` q : Cyc_e → Cyc_m for any order e divisible by m. `}
def order_component_divides (n : Nat) (e : Order) (he : OrderDivides (principal_order (suc. n)) e) (w : CyclesOfOrder e)
  : OrderDivides (principal_order (suc. n)) (cycle_order (w .fst))
  ≔ transport Order (k ↦ OrderDivides (principal_order (suc. n)) k) e (cycle_order (w .fst))
      (inverse Order (cycle_order (w .fst)) e (w .snd)) he

def order_quotient_cycle (n : Nat) (e : Order) (he : OrderDivides (principal_order (suc. n)) e) (w : CyclesOfOrder e)
  : CycleComponent (suc. n)
  ≔ (QuotientCycle n (w .fst), quotient_cycle_standard n (w .fst) (order_component_divides n e he w))

def order_quotient_set (n : Nat) (e : Order) (w : CyclesOfOrder e) : SetTypes
  ≔ (ModQuotient n (w .fst .fst .fst .fst) (w .fst .fst .snd),
     quotient_set (w .fst .fst .fst .fst) (mod_relation n (w .fst .fst .fst .fst) (w .fst .fst .snd)))

def order_quotient_fiber_connected (n : Nat) (e : Order) (he : OrderDivides (principal_order (suc. n)) e)
  (b : Cycles) (hb : Mere (Id Cycles (finite_standard_cycle n) b))
  : Connected (BookFiber (CyclesOfOrder e) Cycles (u ↦ QuotientCycle n (u .fst)) b)
  ≔ let D ≔ CyclesOfOrder e in
    let G ≔ ((u ↦ QuotientCycle n (u .fst)) : D → Cycles) in
    let F ≔ BookFiber D Cycles G b in
    let Bo ≔ ((c ↦ Id Order (cycle_order c) e) : Cycles → Type) in
    (mere_rec (BookFiber Cycles Order cycle_order e) (Mere F) (mere_isprop F)
       (s ↦ let u : D ≔ (s .fst, inverse Order e (cycle_order (s .fst)) (s .snd)) in
         mere_rec (Id Cycles (finite_standard_cycle n) b) (Mere F) (mere_isprop F)
           (β ↦ mere_rec (Id Cycles (finite_standard_cycle n) (G u)) (Mere F) (mere_isprop F)
             (γ ↦ mere F (u, concat Cycles b (finite_standard_cycle n) (G u) (inverse Cycles (finite_standard_cycle n) b β) γ))
             (quotient_cycle_standard n (u .fst) (order_component_divides n e he u)))
           hb)
       (set_trunc_surjective Cycles e),
     v1 v2 ↦
       let d1 ≔ v1 .fst in let d2 ≔ v2 .fst in
       let X1 ≔ d1 .fst .fst .fst .fst in let X2 ≔ d2 .fst .fst .fst .fst in
       let R1 ≔ mod_relation n X1 (d1 .fst .fst .snd) in let R2 ≔ mod_relation n X2 (d2 .fst .fst .snd) in
       let Q1 ≔ ModQuotient n X1 (d1 .fst .fst .snd) in let Q2 ≔ ModQuotient n X2 (d2 .fst .fst .snd) in
       let mp ≔ cycle_order_paths (d2 .fst) (d1 .fst)
         (concat Order (cycle_order (d2 .fst)) e (cycle_order (d1 .fst)) (d2 .snd)
           (inverse Order (cycle_order (d1 .fst)) e (d1 .snd))) in
       mere_rec (b .fst .fst .fst) (Mere (Id F v1 v2)) (mere_isprop (Id F v1 v2))
         (y0 ↦ mere_rec (BookFiber X1 Q1 (quotient_class X1 R1) (cycle_path_evaluate b (G d1) (v1 .snd) y0))
           (Mere (Id F v1 v2)) (mere_isprop (Id F v1 v2))
           (x0 ↦ mere_rec (BookFiber X2 Q2 (quotient_class X2 R2) (cycle_path_evaluate b (G d2) (v2 .snd) y0))
             (Mere (Id F v1 v2)) (mere_isprop (Id F v1 v2))
             (z ↦
               let pp ≔ cycle_periods_imply_pointed (d1 .fst) (d2 .fst) (cycle_paths_imply_periods (d1 .fst) (d2 .fst) mp)
                 (x0 .fst) (z .fst) .center in
               let α ≔ subtype_equal Cycles Bo (c ↦ order_set (cycle_order c) e) d1 d2 (pp .fst) in
               let αfst ≔ equiv_counit (Id D d1 d2) (Id Cycles (d1 .fst) (d2 .fst))
                 (subtype_path_equiv Cycles Bo (c ↦ order_set (cycle_order c) e) d1 d2) (pp .fst) in
               let moved ≔ transport D (u ↦ Id Cycles b (G u)) d1 d2 α (v1 .snd) in
               let E ≔ native_equivalence (Id Cycles b (G d2)) Q2
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

def order_quotient_zero_connected (n : Nat) (e : Order) (he : OrderDivides (principal_order (suc. n)) e)
  : ZeroConnectedMap (CyclesOfOrder e) (CycleComponent (suc. n)) (order_quotient_cycle n e he)
  ≔ connected_fibers_zero_map (CyclesOfOrder e) (CycleComponent (suc. n)) (order_quotient_cycle n e he)
      (w ↦ connected_equiv (BookFiber (CyclesOfOrder e) Cycles (u ↦ QuotientCycle n (u .fst)) (w .fst))
        (BookFiber (CyclesOfOrder e) (CycleComponent (suc. n)) (order_quotient_cycle n e he) w)
        (canonical_inverse_equiv (BookFiber (CyclesOfOrder e) (CycleComponent (suc. n)) (order_quotient_cycle n e he) w)
          (BookFiber (CyclesOfOrder e) Cycles (u ↦ QuotientCycle n (u .fst)) (w .fst))
          (family_equiv (CyclesOfOrder e) (u ↦ Id (CycleComponent (suc. n)) w (order_quotient_cycle n e he u))
            (u ↦ Id Cycles (w .fst) (QuotientCycle n (u .fst)))
            (u ↦ subtype_path_equiv Cycles (x ↦ Mere (Id Cycles (finite_standard_cycle n) x))
              (x ↦ mere_isprop (Id Cycles (finite_standard_cycle n) x)) w (order_quotient_cycle n e he u))))
        .map (order_quotient_fiber_connected n e he (w .fst) (w .snd)))

{` For any order e divisible by m, X ↦ X/m on Cyc_e factors through Cyc_m
   as a 0-image factorization, generalizing thm:image-Z-to-Cm. `}
def order_quotient_factorization (n : Nat) (e : Order) (he : OrderDivides (principal_order (suc. n)) e)
  : ZeroImageFactorizations (CyclesOfOrder e) SetTypes (order_quotient_set n e)
  ≔ (CycleComponent (suc. n), (order_quotient_cycle n e he, (cycle_component_set (suc. n),
      (refl (order_quotient_set n e), (order_quotient_zero_connected n e he, cycle_component_set_covering (suc. n))))))

{` The family of fibers of cdg_m : Cyc_d → Cyc_md. `}
def root_order_fibers (n : Nat) (d : Order) (w : CyclesOfOrder (order_root n d)) : Type
  ≔ BookFiber (CyclesOfOrder d) (CyclesOfOrder (order_root n d)) (cycle_root_of_order n d) w

def root_order_target_periods (n : Nat) (d : Order) (w : CyclesOfOrder (order_root n d))
  : Id (Subtypes Int) (CyclePeriods (w .fst)) (ScaledSubtype (suc. n) (order_periods d))
  ≔ concat (Subtypes Int) (CyclePeriods (w .fst)) (order_periods (order_root n d)) (ScaledSubtype (suc. n) (order_periods d))
      (refl order_periods (w .snd)) (order_root_periods n d)

def root_fiber_order_eq (n : Nat) (d : Order) (w : CyclesOfOrder (order_root n d)) (c : Cycles)
  (p : Id Cycles (w .fst) (cycle_root n c)) : Id Order (cycle_order c) d
  ≔ let S ≔ ScaledSubtype (suc. n) (order_periods d) in
    let wp ≔ root_order_target_periods n d w in
    order_periods_injective (cycle_order c) d
      (concat (Subtypes Int) (CyclePeriods c) (QuotientPeriods n (w .fst)) (order_periods d)
        (root_path_periods n (w .fst) c p)
        (inclusion_antisym Int (QuotientPeriods n (w .fst)) (order_periods d)
          (q h ↦ scaled_member_cancel n (order_periods d) q
            (transport (Subtypes Int) (H ↦ H (int_mul q (pos. (suc. n))) .fst) (CyclePeriods (w .fst)) S wp h))
          (q h ↦ transport (Subtypes Int) (H ↦ H (int_mul q (pos. (suc. n))) .fst) S (CyclePeriods (w .fst))
            (inverse (Subtypes Int) (CyclePeriods (w .fst)) S wp)
            (mere (ScaledWitness (suc. n) (order_periods d) (int_mul q (pos. (suc. n))))
              ((q, refl (int_mul q (pos. (suc. n)))), h)))))

def root_order_fiber_forget (n : Nat) (d : Order) (w : CyclesOfOrder (order_root n d))
  : Equiv (Σ (CyclesOfOrder d) (v ↦ Id Cycles (w .fst) (cycle_root n (v .fst)))) (RootFiber n (w .fst))
  ≔ quasi_inverse_equiv (Σ (CyclesOfOrder d) (v ↦ Id Cycles (w .fst) (cycle_root n (v .fst)))) (RootFiber n (w .fst))
      (v ↦ (v .fst .fst, v .snd))
      (u ↦ ((u .fst, root_fiber_order_eq n d w (u .fst) (u .snd)), u .snd))
      (v ↦ ((refl (v .fst .fst), order_set (cycle_order (v .fst .fst)) d
          (root_fiber_order_eq n d w (v .fst .fst) (v .snd)) (v .fst .snd)), refl (v .snd)))
      (u ↦ refl u)

def root_order_condition (n : Nat) (d : Order) (w : CyclesOfOrder (order_root n d)) : RootFiberCondition n (w .fst)
  ≔ z h ↦ mere_rec (ScaledWitness (suc. n) (order_periods d) z) (Multiples (suc. n) z .fst) (Multiples (suc. n) z .snd)
      (v ↦ mere (MultipleWitness (suc. n) z) (v .fst))
      (transport (Subtypes Int) (H ↦ H z .fst) (CyclePeriods (w .fst)) (ScaledSubtype (suc. n) (order_periods d))
        (root_order_target_periods n d w) h)

{` The fibers of cdg_m : Cyc_d → Cyc_md are the sets X/m. `}
def root_order_fiber_equiv (n : Nat) (d : Order) (w : CyclesOfOrder (order_root n d))
  : Equiv (root_order_fibers n d w) (ModQuotient n (w .fst .fst .fst .fst) (w .fst .fst .snd))
  ≔ let X ≔ w .fst .fst .fst .fst in let Q ≔ ModQuotient n X (w .fst .fst .snd) in
    let P ≔ RootFiberCondition n (w .fst) in
    let A1 ≔ root_order_fibers n d w in
    let A2 ≔ Σ (CyclesOfOrder d) (v ↦ Id Cycles (w .fst) (cycle_root n (v .fst))) in
    let A3 ≔ RootFiber n (w .fst) in
    let e1 ≔ family_equiv (CyclesOfOrder d) (v ↦ Id (CyclesOfOrder (order_root n d)) w (cycle_root_of_order n d v))
      (v ↦ Id Cycles (w .fst) (cycle_root n (v .fst)))
      (v ↦ subtype_path_equiv Cycles (c ↦ Id Order (cycle_order c) (order_root n d))
        (c ↦ order_set (cycle_order c) (order_root n d)) w (cycle_root_of_order n d v)) in
    let e3 ≔ native_equivalence A3 (Product P Q) (root_fiber_equiv n (w .fst)) in
    let pr ≔ root_order_condition n d w in
    let e4 ≔ quasi_inverse_equiv (Product P Q) Q (x ↦ x .snd) (q ↦ (pr, q))
      (x ↦ (root_fiber_condition_prop n (w .fst) pr (x .fst), refl (x .snd))) (q ↦ refl q) in
    compose_equiv A1 (Product P Q) Q
      (compose_equiv A1 A3 (Product P Q) (compose_equiv A1 A2 A3 e1 (root_order_fiber_forget n d w)) e3) e4

def root_order_fiber_set (n : Nat) (d : Order) (w : CyclesOfOrder (order_root n d)) : SetTypes
  ≔ let X ≔ w .fst .fst .fst .fst in let Q ≔ ModQuotient n X (w .fst .fst .snd) in
    (root_order_fibers n d w,
     hlevel_two_to_set (root_order_fibers n d w)
       (hlevel_equiv (suc. (suc. zero.)) Q (root_order_fibers n d w)
         (canonical_inverse_equiv (root_order_fibers n d w) Q (root_order_fiber_equiv n d w))
         (set_to_hlevel_two Q (quotient_set X (mod_relation n X (w .fst .fst .snd))))))

def root_order_fiber_triangle (n : Nat) (d : Order)
  : Id (CyclesOfOrder (order_root n d) → SetTypes) (root_order_fiber_set n d)
      (compose (CyclesOfOrder (order_root n d)) (CycleComponent (suc. n)) SetTypes (cycle_component_set (suc. n))
        (order_quotient_cycle n (order_root n d) (root_order_divides n d)))
  ≔ funext (CyclesOfOrder (order_root n d)) (_ ↦ SetTypes) (root_order_fiber_set n d)
      (compose (CyclesOfOrder (order_root n d)) (CycleComponent (suc. n)) SetTypes (cycle_component_set (suc. n))
        (order_quotient_cycle n (order_root n d) (root_order_divides n d)))
      (w ↦ subtype_equal Type isSet isset_isprop (root_order_fiber_set n d w) (order_quotient_set n (order_root n d) w)
        (ua (root_order_fibers n d w) (ModQuotient n (w .fst .fst .fst .fst) (w .fst .fst .snd)) (root_order_fiber_equiv n d w)))

{` xca:image-Cmd-to-Cm: the family of fibers of cdg_m : Cyc_d → Cyc_md lifts
   to q : Cyc_md → Cyc_m, and this is a 0-image factorization. `}
def root_fibers_factorization (n : Nat) (d : Order)
  : ZeroImageFactorizations (CyclesOfOrder (order_root n d)) SetTypes (root_order_fiber_set n d)
  ≔ (CycleComponent (suc. n), (order_quotient_cycle n (order_root n d) (root_order_divides n d),
      (cycle_component_set (suc. n), (root_order_fiber_triangle n d,
        (order_quotient_zero_connected n (order_root n d) (root_order_divides n d), cycle_component_set_covering (suc. n))))))
