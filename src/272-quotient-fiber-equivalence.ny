export "271-quotient-fiber-maps"

{` The identification (X,t) = (Fin m × V, ᵐ√(t^m)) used for φ∘ψ:
   (k, v) ↦ t^k(v). `}
def class_unwind (n : Nat) (Y : Cycles) (V : ModQuotient n (Y .fst .fst .fst) (Y .fst .snd))
  (z : Product (Fin (suc. n)) (ClassCarrier n Y V)) : Y .fst .fst .fst
  ≔ iterate (Y .fst .fst .fst) (Y .fst .snd .map) (fin_book_below_equiv (suc. n) .map (z .fst) .fst) (z .snd .fst)

def class_unwind_remainder (n : Nat) (Y : Cycles) (V : ModQuotient n (Y .fst .fst .fst) (Y .fst .snd))
  (z : Product (Remainder (suc. n)) (ClassCarrier n Y V)) : Y .fst .fst .fst
  ≔ iterate (Y .fst .fst .fst) (Y .fst .snd .map) (z .fst .fst) (z .snd .fst)

def class_unwind_remainder_step (n : Nat) (Y : Cycles) (V : ModQuotient n (Y .fst .fst .fst) (Y .fst .snd))
  (z : Product (Remainder (suc. n)) (ClassCarrier n Y V))
  : Id (Y .fst .fst .fst)
      (class_unwind_remainder n Y V (root_remainder n (ClassCarrier n Y V) (class_permutation n Y V .map) z))
      (Y .fst .snd .map (class_unwind_remainder n Y V z))
  ≔ match le_split (z .fst .fst) n (lt_from_book (z .fst .fst) (suc. n) (z .fst .snd)) [
  | inl. small ↦ refl (class_unwind_remainder n Y V)
      (root_remainder_small n (ClassCarrier n Y V) (class_permutation n Y V .map) (z .fst) small (z .snd))
  | inr. last ↦ concat (Y .fst .fst .fst)
      (class_unwind_remainder n Y V (root_remainder n (ClassCarrier n Y V) (class_permutation n Y V .map) z))
      (class_unwind_remainder n Y V (remainder_at n zero. star., class_permutation n Y V .map (z .snd)))
      (Y .fst .snd .map (class_unwind_remainder n Y V z))
      (refl (class_unwind_remainder n Y V)
        (root_remainder_last_at n (ClassCarrier n Y V) (class_permutation n Y V .map) (z .fst) last (z .snd)))
      (refl ((k ↦ Y .fst .snd .map (iterate (Y .fst .fst .fst) (Y .fst .snd .map) k (z .snd .fst))) : Nat → Y .fst .fst .fst)
        (inverse Nat (z .fst .fst) n last)) ]

def class_unwind_commutes (n : Nat) (Y : Cycles) (V : ModQuotient n (Y .fst .fst .fst) (Y .fst .snd))
  : Commutes (Product (Fin (suc. n)) (ClassCarrier n Y V)) (Y .fst .fst .fst)
      (root_finite_equiv n (ClassCarrier n Y V) (class_permutation n Y V)) (Y .fst .snd) (class_unwind n Y V)
  ≔ z ↦ concat (Y .fst .fst .fst)
      (class_unwind n Y V (root_finite n (ClassCarrier n Y V) (class_permutation n Y V .map) z))
      (class_unwind_remainder n Y V
        (root_remainder n (ClassCarrier n Y V) (class_permutation n Y V .map) (root_finite_encode n (ClassCarrier n Y V) z)))
      (Y .fst .snd .map (class_unwind n Y V z))
      (refl ((r ↦ iterate (Y .fst .fst .fst) (Y .fst .snd .map) (r .fst)
            (root_remainder n (ClassCarrier n Y V) (class_permutation n Y V .map) (root_finite_encode n (ClassCarrier n Y V) z)
              .snd .fst)) : Remainder (suc. n) → Y .fst .fst .fst)
        (equiv_counit (Fin (suc. n)) (Remainder (suc. n)) (fin_book_below_equiv (suc. n))
          (root_remainder n (ClassCarrier n Y V) (class_permutation n Y V .map) (root_finite_encode n (ClassCarrier n Y V) z) .fst)))
      (class_unwind_remainder_step n Y V (root_finite_encode n (ClassCarrier n Y V) z))

def class_unwind_back (n : Nat) (y : CycleComponent zero.) (V : ModQuotient n (y .fst .fst .fst .fst) (y .fst .fst .snd))
  : PeriodInclusion (y .fst .fst .fst .fst) (Product (Fin (suc. n)) (ClassCarrier n (y .fst) V)) (y .fst .fst .snd)
      (root_finite_equiv n (ClassCarrier n (y .fst) V) (class_permutation n (y .fst) V))
  ≔ z hz ↦ transport Int
      (PowerPeriod (Product (Fin (suc. n)) (ClassCarrier n (y .fst) V))
        (root_finite_equiv n (ClassCarrier n (y .fst) V) (class_permutation n (y .fst) V)))
      int_zero z
      (inverse Int z int_zero (infinite_period_is_zero z
        (transport (Subtypes Int) (H ↦ H z .fst) (CyclePeriods (y .fst)) (CyclePeriods infinite_cycle)
          (inverse (Subtypes Int) (CyclePeriods infinite_cycle) (CyclePeriods (y .fst))
            (cycle_paths_imply_periods infinite_cycle (y .fst) (y .snd))) hz)))
      (power_period_zero (Product (Fin (suc. n)) (ClassCarrier n (y .fst) V))
        (root_finite_equiv n (ClassCarrier n (y .fst) V) (class_permutation n (y .fst) V)))

def class_unwind_equiv (n : Nat) (y : CycleComponent zero.) (V : ModQuotient n (y .fst .fst .fst .fst) (y .fst .fst .snd))
  : Equiv (Product (Fin (suc. n)) (ClassCarrier n (y .fst) V)) (y .fst .fst .fst .fst)
  ≔ cycle_map_equiv (Product (Fin (suc. n)) (ClassCarrier n (y .fst) V)) (y .fst .fst .fst .fst)
      (sigma_set (Fin (suc. n)) (_ ↦ ClassCarrier n (y .fst) V) (fin_set (suc. n)) (_ ↦ class_carrier_set n (y .fst) V))
      (y .fst .fst .fst .snd)
      (root_finite_equiv n (ClassCarrier n (y .fst) V) (class_permutation n (y .fst) V)) (y .fst .fst .snd)
      (root_finite_cyclic n (ClassCarrier n (y .fst) V) (class_permutation n (y .fst) V) (class_cyclic n (y .fst) V))
      (y .fst .snd)
      (class_unwind n (y .fst) V, class_unwind_commutes n (y .fst) V) (class_unwind_back n y V)

{` Transport in the fiber family commutes with forgetting the component. `}
def quotient_fiber_transport_fst (n : Nat) (a1 a2 : CycleComponent zero.) (α : Id (CycleComponent zero.) a1 a2)
  (r : Id (CycleComponent (suc. n)) (principal_component_point (suc. n)) (infinite_quotient_cycle n a1))
  : Id (Id Cycles (finite_standard_cycle n) (QuotientCycle n (a2 .fst)))
      (transport (CycleComponent zero.)
        (x ↦ Id (CycleComponent (suc. n)) (principal_component_point (suc. n)) (infinite_quotient_cycle n x)) a1 a2 α r .fst)
      (transport (CycleComponent zero.)
        (x ↦ Id Cycles (finite_standard_cycle n) (QuotientCycle n (x .fst))) a1 a2 α (r .fst))
  ≔ J (CycleComponent zero.) a1
      (a2 α ↦ (r : Id (CycleComponent (suc. n)) (principal_component_point (suc. n)) (infinite_quotient_cycle n a1))
        → Id (Id Cycles (finite_standard_cycle n) (QuotientCycle n (a2 .fst)))
            (transport (CycleComponent zero.)
              (x ↦ Id (CycleComponent (suc. n)) (principal_component_point (suc. n)) (infinite_quotient_cycle n x)) a1 a2 α r .fst)
            (transport (CycleComponent zero.)
              (x ↦ Id Cycles (finite_standard_cycle n) (QuotientCycle n (x .fst))) a1 a2 α (r .fst)))
      (r ↦ concat (Id Cycles (finite_standard_cycle n) (QuotientCycle n (a1 .fst)))
        (transport (CycleComponent zero.)
          (x ↦ Id (CycleComponent (suc. n)) (principal_component_point (suc. n)) (infinite_quotient_cycle n x)) a1 a1 (refl a1) r .fst)
        (r .fst)
        (transport (CycleComponent zero.)
          (x ↦ Id Cycles (finite_standard_cycle n) (QuotientCycle n (x .fst))) a1 a1 (refl a1) (r .fst))
        (refl ((s ↦ s .fst) : Id (CycleComponent (suc. n)) (principal_component_point (suc. n)) (infinite_quotient_cycle n a1)
              → Id Cycles (finite_standard_cycle n) (QuotientCycle n (a1 .fst)))
          (transport_refl (CycleComponent zero.)
            (x ↦ Id (CycleComponent (suc. n)) (principal_component_point (suc. n)) (infinite_quotient_cycle n x)) a1 r))
        (inverse (Id Cycles (finite_standard_cycle n) (QuotientCycle n (a1 .fst)))
          (transport (CycleComponent zero.)
            (x ↦ Id Cycles (finite_standard_cycle n) (QuotientCycle n (x .fst))) a1 a1 (refl a1) (r .fst))
          (r .fst)
          (transport_refl (CycleComponent zero.) (x ↦ Id Cycles (finite_standard_cycle n) (QuotientCycle n (x .fst))) a1 (r .fst))))
      a2 α r

{` φ ∘ ψ = id. `}
def quotient_fiber_phi_psi (n : Nat) (w : QuotientFiber n)
  : Id (QuotientFiber n) (quotient_fiber_phi n (quotient_fiber_psi n w)) w
  ≔ let D ≔ CycleComponent zero. in
    let y ≔ w .fst in let Y ≔ y .fst in let X' ≔ Y .fst .fst .fst in let u' ≔ Y .fst .snd in
    let V ≔ quotient_fiber_class n w in
    let v ≔ class_cycle n Y V in let C ≔ ClassCarrier n Y V in
    let a1 ≔ cycle_root_component n zero. (quotient_fiber_psi n w) in
    let Cm ≔ CycleComponent (suc. n) in let pt ≔ principal_component_point (suc. n) in
    let std ≔ finite_standard_cycle n in
    let z0r : Remainder (suc. n) ≔ remainder_at n zero. star. in
    let Bm ≔ ((x ↦ Mere (Id Cycles std x)) : Cycles → Type) in
    let hBm ≔ ((x ↦ mere_isprop (Id Cycles std x)) : (x : Cycles) → isProp (Bm x)) in
    let Binf ≔ ((x ↦ Mere (Id Cycles infinite_cycle x)) : Cycles → Type) in
    let hBinf ≔ ((x ↦ mere_isprop (Id Cycles infinite_cycle x)) : (x : Cycles) → isProp (Binf x)) in
    let G ≔ ((x ↦ QuotientCycle n (x .fst)) : D → Cycles) in
    let fam ≔ ((x ↦ Id Cm pt (infinite_quotient_cycle n x)) : D → Type) in
    let P2 ≔ quotient_fiber_phi n (quotient_fiber_psi n w) .snd in
    let iso ≔ ((class_unwind_equiv n y V, class_unwind_commutes n Y V) : PermutationIsomorphisms (cycle_root n v .fst) (Y .fst)) in
    let alpha ≔ equiv_inverse_map (Id Cycles (cycle_root n v) Y) (PermutationIsomorphisms (cycle_root n v .fst) (Y .fst))
      (cycle_paths_equiv (cycle_root n v) Y) iso in
    let aD ≔ subtype_equal Cycles Binf hBinf a1 y alpha in
    let aDfst ≔ equiv_counit (Id D a1 y) (Id Cycles (cycle_root n v) Y) (subtype_path_equiv Cycles Binf hBinf a1 y) alpha in
    let P2fst ≔ equiv_counit (Id Cm pt (infinite_quotient_cycle n a1)) (Id Cycles std (QuotientCycle n (cycle_root n v)))
      (subtype_path_equiv Cycles Bm hBm pt (infinite_quotient_cycle n a1)) (root_quotient_path n v) in
    let moved ≔ transport D fam a1 y aD P2 in
    let QY ≔ ModQuotient n X' u' in let RY ≔ mod_relation n X' u' in
    let F ≔ Product (Fin (suc. n)) C in
    let Rr ≔ mod_relation n F (root_finite_equiv n C (class_permutation n Y V)) in
    let Qr ≔ ModQuotient n F (root_finite_equiv n C (class_permutation n Y V)) in
    let zc ≔ equiv_inverse_map Qr (Remainder (suc. n)) (first_residue_equiv n v) z0r in
    let ev ≔ ((r ↦ cycle_path_evaluate std (QuotientCycle n Y) r z0r) : Id Cycles std (QuotientCycle n Y) → QY) in
    let evq ≔ ((q ↦ cycle_path_evaluate (G a1) (G y) (refl G aD) q) : Qr → QY) in
    let same_eval ≔ mere_rec (BookFiber F Qr (quotient_class F Rr) zc) (Id QY (ev (moved .fst)) (ev (w .snd .fst)))
      (quotient_set X' RY (ev (moved .fst)) (ev (w .snd .fst)))
      (z0 ↦ calc
        ev (moved .fst) = ev (transport D (x ↦ Id Cycles std (G x)) a1 y aD (P2 .fst))
          by refl ev (quotient_fiber_transport_fst n a1 y aD P2)
        = evq (cycle_path_evaluate std (G a1) (P2 .fst) z0r)
          by cycle_path_family_transport_evaluate D G std a1 y aD (P2 .fst) z0r
        = evq (cycle_path_evaluate std (G a1) (root_quotient_path n v) z0r)
          by refl ((r ↦ evq (cycle_path_evaluate std (G a1) r z0r)) : Id Cycles std (G a1) → QY) P2fst
        = evq zc by refl evq (root_quotient_path_zero n v)
        = evq (quotient_class F Rr (z0 .fst)) by refl evq (z0 .snd)
        = quotient_class X' RY (cycle_path_evaluate (a1 .fst) Y (refl ((x ↦ x .fst) : D → Cycles) aD) (z0 .fst))
          by quotient_cycle_ap_evaluate n D (x ↦ x .fst) a1 y aD (z0 .fst)
        = quotient_class X' RY (cycle_path_evaluate (cycle_root n v) Y alpha (z0 .fst))
          by refl ((r ↦ quotient_class X' RY (cycle_path_evaluate (cycle_root n v) Y r (z0 .fst))) : Id Cycles (cycle_root n v) Y → QY) aDfst
        = quotient_class X' RY (class_unwind n Y V (z0 .fst))
          by refl (quotient_class X' RY) (iso_path_evaluate (cycle_root n v) Y iso (z0 .fst))
        = quotient_class X' RY (z0 .fst .snd .fst)
          by refl ((k ↦ quotient_class X' RY (iterate X' (u' .map) (fin_book_below_equiv (suc. n) .map k .fst) (z0 .fst .snd .fst)))
              : Fin (suc. n) → QY)
            (first_zero_class_elim n v (z0 .fst) (inverse Qr zc (quotient_class F Rr (z0 .fst)) (z0 .snd)))
        = V by inverse QY V (quotient_class X' RY (z0 .fst .snd .fst))
          (equiv_inverse_map (Id QY V (quotient_class X' RY (z0 .fst .snd .fst))) (V .fst (z0 .fst .snd .fst) .fst)
            (quotient_class_property X' RY V (z0 .fst .snd .fst)) (z0 .fst .snd .snd)) ∎)
      (quotient_surjective F Rr zc) in
    let same_cycles ≔ equivalence_injective (Id Cycles std (QuotientCycle n Y)) QY
      (native_equivalence (Id Cycles std (QuotientCycle n Y)) QY
        (cycle_evaluation_from_component std (QuotientCycle n Y) (mere (Id Cycles std (QuotientCycle n Y)) (w .snd .fst)) z0r))
      (moved .fst) (w .snd .fst) same_eval in
    let same ≔ equivalence_injective (Id Cm pt (infinite_quotient_cycle n y)) (Id Cycles std (QuotientCycle n Y))
      (subtype_path_equiv Cycles Bm hBm pt (infinite_quotient_cycle n y)) moved (w .snd) same_cycles in
    (aD, pathover_of_eq D fam a1 y aD P2 (w .snd) same)

{` Exercise after thm:image-Z-to-Cm: φ and ψ are mutually inverse, so the
   fiber of q at the standard m-cycle is identified with Cyc_0. `}
def quotient_fiber_equiv (n : Nat) : Equiv (CycleComponent zero.) (QuotientFiber n)
  ≔ quasi_inverse_equiv (CycleComponent zero.) (QuotientFiber n) (quotient_fiber_phi n) (quotient_fiber_psi n)
      (quotient_fiber_psi_phi n) (quotient_fiber_phi_psi n)

{` Hence this fiber is connected, as the printed proof concludes. `}
def quotient_fiber_connected (n : Nat) : Connected (QuotientFiber n)
  ≔ connected_equiv (CycleComponent zero.) (QuotientFiber n) (quotient_fiber_equiv n) .map
      (native_component_connected Cycles infinite_cycle)
