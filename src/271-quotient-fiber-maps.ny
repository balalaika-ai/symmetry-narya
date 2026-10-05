export "270-class-cycles"

{` The residue (k,x) ↦ k on the m-th root: it preserves the cycle structure
   and induces e : (Fin m × X)/m ≃ ℤ/m, [(k,x)] ↦ k. `}
def first_residue (n : Nat) (c : Cycles) : CycleResidues n (cycle_root n c)
  ≔ ((w ↦ fin_book_below_equiv (suc. n) .map (w .fst)), root_finite_remainder_first n (c .fst .fst .fst) (c .fst .snd))

def first_residue_equiv (n : Nat) (c : Cycles)
  : Equiv (ModQuotient n (Product (Fin (suc. n)) (c .fst .fst .fst)) (root_finite_equiv n (c .fst .fst .fst) (c .fst .snd)))
      (Remainder (suc. n))
  ≔ residue_quotient_equiv n (cycle_root n c) (first_residue n c)

{` e⁻¹ as an identification pt_m = q(cdg_m(X,t)). `}
def root_quotient_path (n : Nat) (c : Cycles)
  : Id Cycles (finite_standard_cycle n) (QuotientCycle n (cycle_root n c))
  ≔ inverse Cycles (QuotientCycle n (cycle_root n c)) (finite_standard_cycle n)
      (quotient_cycle_residue_path n (cycle_root n c) (first_residue n c))

def root_quotient_path_zero (n : Nat) (c : Cycles)
  : Id (ModQuotient n (Product (Fin (suc. n)) (c .fst .fst .fst)) (root_finite_equiv n (c .fst .fst .fst) (c .fst .snd)))
      (cycle_path_evaluate (finite_standard_cycle n) (QuotientCycle n (cycle_root n c)) (root_quotient_path n c)
        (remainder_at n zero. star.))
      (equiv_inverse_map (ModQuotient n (Product (Fin (suc. n)) (c .fst .fst .fst)) (root_finite_equiv n (c .fst .fst .fst) (c .fst .snd)))
        (Remainder (suc. n)) (first_residue_equiv n c) (remainder_at n zero. star.))
  ≔ let Q ≔ QuotientCycle n (cycle_root n c) in
    let Qc ≔ ModQuotient n (Product (Fin (suc. n)) (c .fst .fst .fst)) (root_finite_equiv n (c .fst .fst .fst) (c .fst .snd)) in
    let E ≔ first_residue_equiv n c in
    let qp ≔ quotient_cycle_residue_path n (cycle_root n c) (first_residue n c) in
    let back ≔ cycle_path_evaluate (finite_standard_cycle n) Q (inverse Cycles Q (finite_standard_cycle n) qp) in
    let v ≔ equiv_inverse_map Qc (Remainder (suc. n)) E (remainder_at n zero. star.) in
    calc
      back (remainder_at n zero. star.) = back (E .map v)
        by refl back (inverse (Remainder (suc. n)) (E .map v) (remainder_at n zero. star.)
          (equiv_counit Qc (Remainder (suc. n)) E (remainder_at n zero. star.)))
      = back (cycle_path_evaluate Q (finite_standard_cycle n) qp v)
        by refl back (inverse (Remainder (suc. n)) (cycle_path_evaluate Q (finite_standard_cycle n) qp v) (E .map v)
          (iso_path_evaluate Q (finite_standard_cycle n)
            (residue_quotient_equiv n (cycle_root n c) (first_residue n c),
             residue_quotient_commutes n (cycle_root n c) (first_residue n c)) v))
      = v by cycle_path_evaluate_inverse Q (finite_standard_cycle n) qp v ∎

{` The class e⁻¹(0) consists of the pairs (0, x). `}
def first_zero_class_intro (n : Nat) (c : Cycles) (x : c .fst .fst .fst)
  : Id (ModQuotient n (Product (Fin (suc. n)) (c .fst .fst .fst)) (root_finite_equiv n (c .fst .fst .fst) (c .fst .snd)))
      (quotient_class (Product (Fin (suc. n)) (c .fst .fst .fst))
        (mod_relation n (Product (Fin (suc. n)) (c .fst .fst .fst)) (root_finite_equiv n (c .fst .fst .fst) (c .fst .snd)))
        (inr. star., x))
      (equiv_inverse_map (ModQuotient n (Product (Fin (suc. n)) (c .fst .fst .fst)) (root_finite_equiv n (c .fst .fst .fst) (c .fst .snd)))
        (Remainder (suc. n)) (first_residue_equiv n c) (remainder_at n zero. star.))
  ≔ let F ≔ Product (Fin (suc. n)) (c .fst .fst .fst) in
    let R ≔ mod_relation n F (root_finite_equiv n (c .fst .fst .fst) (c .fst .snd)) in
    let Qc ≔ ModQuotient n F (root_finite_equiv n (c .fst .fst .fst) (c .fst .snd)) in
    let E ≔ first_residue_equiv n c in
    equiv_inverse_map (Id Qc (quotient_class F R (inr. star., x)) (equiv_inverse_map Qc (Remainder (suc. n)) E (remainder_at n zero. star.)))
      (Id (Remainder (suc. n)) (E .map (quotient_class F R (inr. star., x))) (remainder_at n zero. star.))
      (equiv_inverse_characterization Qc (Remainder (suc. n)) (quotient_set F R) (remainder_set (suc. n)) E
        (quotient_class F R (inr. star., x)) (remainder_at n zero. star.))
      (remainder_equal (suc. n) (E .map (quotient_class F R (inr. star., x))) (remainder_at n zero. star.) (refl (zero. : Nat)))

def first_zero_class_elim (n : Nat) (c : Cycles) (w : Product (Fin (suc. n)) (c .fst .fst .fst))
  (s : Id (ModQuotient n (Product (Fin (suc. n)) (c .fst .fst .fst)) (root_finite_equiv n (c .fst .fst .fst) (c .fst .snd)))
    (quotient_class (Product (Fin (suc. n)) (c .fst .fst .fst))
      (mod_relation n (Product (Fin (suc. n)) (c .fst .fst .fst)) (root_finite_equiv n (c .fst .fst .fst) (c .fst .snd))) w)
    (equiv_inverse_map (ModQuotient n (Product (Fin (suc. n)) (c .fst .fst .fst)) (root_finite_equiv n (c .fst .fst .fst) (c .fst .snd)))
      (Remainder (suc. n)) (first_residue_equiv n c) (remainder_at n zero. star.)))
  : Id (Fin (suc. n)) (w .fst) (inr. star.)
  ≔ let F ≔ Product (Fin (suc. n)) (c .fst .fst .fst) in
    let R ≔ mod_relation n F (root_finite_equiv n (c .fst .fst .fst) (c .fst .snd)) in
    let Qc ≔ ModQuotient n F (root_finite_equiv n (c .fst .fst .fst) (c .fst .snd)) in
    let E ≔ first_residue_equiv n c in
    let fbb ≔ fin_book_below_equiv (suc. n) in
    equivalence_injective (Fin (suc. n)) (Remainder (suc. n)) fbb (w .fst) (inr. star.)
      (concat (Remainder (suc. n)) (fbb .map (w .fst)) (remainder_at n zero. star.) (fbb .map (inr. star.))
        (equiv_inverse_characterization Qc (Remainder (suc. n)) (quotient_set F R) (remainder_set (suc. n)) E
          (quotient_class F R w) (remainder_at n zero. star.) .map s)
        (remainder_equal (suc. n) (remainder_at n zero. star.) (fbb .map (inr. star.)) (refl (zero. : Nat))))

{` The preimage q⁻¹(pt_m) of the standard m-cycle, book orientation. `}
def QuotientFiber (n : Nat) : Type
  ≔ BookFiber (CycleComponent zero.) (CycleComponent (suc. n)) (infinite_quotient_cycle n) (principal_component_point (suc. n))

{` φ(X,t) ≔ (cdg_m(X,t), e⁻¹). `}
def quotient_fiber_phi (n : Nat) (u : CycleComponent zero.) : QuotientFiber n
  ≔ (cycle_root_component n zero. u,
      subtype_equal Cycles (x ↦ Mere (Id Cycles (finite_standard_cycle n) x))
        (x ↦ mere_isprop (Id Cycles (finite_standard_cycle n) x))
        (principal_component_point (suc. n)) (infinite_quotient_cycle n (cycle_root_component n zero. u))
        (root_quotient_path n (u .fst)))

{` ψ((Y,u), e') ≔ (e'(0), u^m), with e'(0) ⊆ Y a class of Y/m. `}
def quotient_fiber_class (n : Nat) (w : QuotientFiber n) : ModQuotient n (w .fst .fst .fst .fst .fst) (w .fst .fst .fst .snd)
  ≔ cycle_path_evaluate (finite_standard_cycle n) (QuotientCycle n (w .fst .fst)) (w .snd .fst) (remainder_at n zero. star.)

def quotient_fiber_psi (n : Nat) (w : QuotientFiber n) : CycleComponent zero.
  ≔ (class_cycle n (w .fst .fst) (quotient_fiber_class n w), class_cycle_infinite n (w .fst) (quotient_fiber_class n w))

{` ψ ∘ φ = id. `}
def quotient_fiber_psi_phi (n : Nat) (u : CycleComponent zero.)
  : Id (CycleComponent zero.) (quotient_fiber_psi n (quotient_fiber_phi n u)) u
  ≔ let c ≔ u .fst in let X ≔ c .fst .fst .fst in let t ≔ c .fst .snd in
    let F ≔ Product (Fin (suc. n)) X in let rc ≔ cycle_root n c in
    let R ≔ mod_relation n F (root_finite_equiv n X t) in
    let Qc ≔ ModQuotient n F (root_finite_equiv n X t) in
    let E ≔ first_residue_equiv n c in
    let zero_class ≔ equiv_inverse_map Qc (Remainder (suc. n)) E (remainder_at n zero. star.) in
    let Bm ≔ ((x ↦ Mere (Id Cycles (finite_standard_cycle n) x)) : Cycles → Type) in
    let V ≔ quotient_fiber_class n (quotient_fiber_phi n u) in
    let s1 ≔ concat Qc V
      (cycle_path_evaluate (finite_standard_cycle n) (QuotientCycle n rc) (root_quotient_path n c) (remainder_at n zero. star.))
      zero_class
      (refl ((r ↦ cycle_path_evaluate (finite_standard_cycle n) (QuotientCycle n rc) r (remainder_at n zero. star.))
          : Id Cycles (finite_standard_cycle n) (QuotientCycle n rc) → Qc)
        (equiv_counit (Id (CycleComponent (suc. n)) (principal_component_point (suc. n))
            (infinite_quotient_cycle n (cycle_root_component n zero. u)))
          (Id Cycles (finite_standard_cycle n) (QuotientCycle n rc))
          (subtype_path_equiv Cycles Bm (x ↦ mere_isprop (Id Cycles (finite_standard_cycle n) x))
            (principal_component_point (suc. n)) (infinite_quotient_cycle n (cycle_root_component n zero. u)))
          (root_quotient_path n c)))
      (root_quotient_path_zero n c) in
    let mem_intro ≔ ((x ↦ quotient_class_property F R V (inr. star., x) .map
        (concat Qc V zero_class (quotient_class F R (inr. star., x)) s1
          (inverse Qc (quotient_class F R (inr. star., x)) zero_class (first_zero_class_intro n c x))))
      : (x : X) → V .fst (inr. star., x) .fst) in
    let mem_elim ≔ ((w h ↦ first_zero_class_elim n c w
        (concat Qc (quotient_class F R w) V zero_class
          (inverse Qc V (quotient_class F R w)
            (equiv_inverse_map (Id Qc V (quotient_class F R w)) (V .fst w .fst) (quotient_class_property F R V w) h))
          s1))
      : (w : F) → V .fst w .fst → Id (Fin (suc. n)) (w .fst) (inr. star.)) in
    let C ≔ ClassCarrier n rc V in
    let f ≔ ((x ↦ ((inr. star., x), mem_intro x)) : X → C) in
    let g ≔ ((w ↦ w .fst .snd) : C → X) in
    let e ≔ quasi_inverse_equiv X C f g (x ↦ refl x)
      (w ↦ subtype_equal F (z ↦ V .fst z .fst) (z ↦ V .fst z .snd) (f (g w)) w
        (inverse (Fin (suc. n)) (w .fst .fst) (inr. star.) (mem_elim (w .fst) (w .snd)), refl (w .fst .snd))) in
    let commute ≔ ((x ↦ subtype_equal F (z ↦ V .fst z .fst) (z ↦ V .fst z .snd) (f (t .map x))
        (class_permutation n rc V .map (f x))
        (inverse F (iterate F (root_finite n X (t .map)) (suc. n) (inr. star., x)) (inr. star., t .map x)
          (root_finite_full_turn n X (t .map) (inr. star., x))))
      : Commutes X C t (class_permutation n rc V) (e .map)) in
    let alpha ≔ equiv_inverse_map (Id Cycles c (class_cycle n rc V))
      (PermutationIsomorphisms (c .fst) (class_cycle n rc V .fst)) (cycle_paths_equiv c (class_cycle n rc V)) (e, commute) in
    subtype_equal Cycles (x ↦ Mere (Id Cycles infinite_cycle x)) (x ↦ mere_isprop (Id Cycles infinite_cycle x))
      (quotient_fiber_psi n (quotient_fiber_phi n u)) u (inverse Cycles c (class_cycle n rc V) alpha)
