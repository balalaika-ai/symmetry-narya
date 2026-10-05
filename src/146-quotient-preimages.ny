export "145-order-quotient-images"

{` Identifications (ℤ/m, s) = (X/m, t̄), as isomorphisms of permutations. `}
def StandardQuotientIsos (n : Nat) (c : Cycles) : Type
  ≔ PermutationIsomorphisms (finite_standard_cycle n .fst) (QuotientCycle n c .fst)

def iso_residue (n : Nat) (c : Cycles) (i : StandardQuotientIsos n c) : CycleResidues n c
  ≔ let X ≔ c .fst .fst .fst in let R ≔ mod_relation n X (c .fst .snd) in
    let Q ≔ ModQuotient n X (c .fst .snd) in let Rem ≔ Remainder (suc. n) in
    let e ≔ i .fst in let g ≔ equiv_inverse_map Rem Q e in
    let T ≔ quotient_successor n c in
    ((x ↦ g (quotient_class X R x)),
     x ↦ let V ≔ quotient_class X R x in calc
       g (T V) = g (T (e .map (g V)))
         by refl ((W ↦ g (T W)) : Q → Rem) (inverse Q (e .map (g V)) V (equiv_counit Rem Q e V))
       = g (e .map (modular_successor n (g V)))
         by refl g (inverse Q (e .map (modular_successor n (g V))) (T (e .map (g V))) (i .snd (g V)))
       = modular_successor n (g V) by equiv_retraction Rem Q e (modular_successor n (g V)) ∎)

def residue_iso (n : Nat) (c : Cycles) (rho : CycleResidues n c) : StandardQuotientIsos n c
  ≔ let X ≔ c .fst .fst .fst in let Q ≔ ModQuotient n X (c .fst .snd) in let Rem ≔ Remainder (suc. n) in
    let E ≔ residue_quotient_equiv n c rho in let h ≔ equiv_inverse_map Q Rem E in
    let T ≔ quotient_successor n c in
    (canonical_inverse_equiv Q Rem E,
     r ↦ calc
       h (modular_successor n r) = h (modular_successor n (E .map (h r)))
         by refl ((s ↦ h (modular_successor n s)) : Rem → Q) (inverse Rem (E .map (h r)) r (equiv_counit Q Rem E r))
       = h (E .map (T (h r)))
         by refl h (inverse Rem (E .map (T (h r))) (modular_successor n (E .map (h r))) (residue_quotient_commutes n c rho (h r)))
       = T (h r) by equiv_retraction Q Rem E (T (h r)) ∎)

def double_inverse_map (A B : Type) (e : Equiv A B) (a : A)
  : Id B (equiv_inverse_map B A (canonical_inverse_equiv A B e) a) (e .map a)
  ≔ inverse_at_known_point B A (canonical_inverse_equiv A B e) (e .map a) a (equiv_retraction A B e a)

def residues_set (n : Nat) (c : Cycles) : isSet (CycleResidues n c)
  ≔ sigma_set (c .fst .fst .fst → Remainder (suc. n))
      (h ↦ Commutes (c .fst .fst .fst) (Remainder (suc. n)) (c .fst .snd) (modular_successor_equiv n) h)
      (pi_set (c .fst .fst .fst) (_ ↦ Remainder (suc. n)) (_ ↦ remainder_set (suc. n)))
      (h ↦ prop_is_set (Commutes (c .fst .fst .fst) (Remainder (suc. n)) (c .fst .snd) (modular_successor_equiv n) h)
        (commutes_prop (c .fst .fst .fst) (Remainder (suc. n)) (remainder_set (suc. n)) (c .fst .snd) (modular_successor_equiv n) h))

def residue_equal (n : Nat) (c : Cycles) (rho sigma : CycleResidues n c)
  (p : (x : c .fst .fst .fst) → Id (Remainder (suc. n)) (rho .fst x) (sigma .fst x)) : Id (CycleResidues n c) rho sigma
  ≔ subtype_equal (c .fst .fst .fst → Remainder (suc. n))
      (h ↦ Commutes (c .fst .fst .fst) (Remainder (suc. n)) (c .fst .snd) (modular_successor_equiv n) h)
      (h ↦ commutes_prop (c .fst .fst .fst) (Remainder (suc. n)) (remainder_set (suc. n)) (c .fst .snd) (modular_successor_equiv n) h)
      rho sigma (funext (c .fst .fst .fst) (_ ↦ Remainder (suc. n)) (rho .fst) (sigma .fst) p)

def residue_quotient_is_inverse (n : Nat) (c : Cycles) (i : StandardQuotientIsos n c)
  (V : ModQuotient n (c .fst .fst .fst) (c .fst .snd))
  : Id (Remainder (suc. n)) (residue_quotient_map n c (iso_residue n c i) V)
      (equiv_inverse_map (Remainder (suc. n)) (ModQuotient n (c .fst .fst .fst) (c .fst .snd)) (i .fst) V)
  ≔ let X ≔ c .fst .fst .fst in let R ≔ mod_relation n X (c .fst .snd) in
    quotient_prop_induction X R
      (V ↦ Id (Remainder (suc. n)) (residue_quotient_map n c (iso_residue n c i) V)
        (equiv_inverse_map (Remainder (suc. n)) (ModQuotient n X (c .fst .snd)) (i .fst) V))
      (V ↦ remainder_set (suc. n) (residue_quotient_map n c (iso_residue n c i) V)
        (equiv_inverse_map (Remainder (suc. n)) (ModQuotient n X (c .fst .snd)) (i .fst) V))
      (x ↦ refl (equiv_inverse_map (Remainder (suc. n)) (ModQuotient n X (c .fst .snd)) (i .fst) (quotient_class X R x))) V

def standard_quotient_isos_residues (n : Nat) (c : Cycles)
  : Equiv (StandardQuotientIsos n c) (CycleResidues n c)
  ≔ let X ≔ c .fst .fst .fst in let R ≔ mod_relation n X (c .fst .snd) in
    let Q ≔ ModQuotient n X (c .fst .snd) in let Rem ≔ Remainder (suc. n) in
    let Iso ≔ StandardQuotientIsos n c in
    let comm ≔ ((e ↦ Commutes Rem Q (modular_successor_equiv n) (quotient_successor_equiv n c) (e .map)) : Equiv Rem Q → Type) in
    quasi_inverse_equiv Iso (CycleResidues n c) (iso_residue n c) (residue_iso n c)
      (i ↦ subtype_equal (Equiv Rem Q) comm
        (e ↦ commutes_prop Rem Q (quotient_set X R) (modular_successor_equiv n) (quotient_successor_equiv n c) (e .map))
        (residue_iso n c (iso_residue n c i)) i
        (equiv_path Rem Q (canonical_inverse_equiv Q Rem (residue_quotient_equiv n c (iso_residue n c i))) (i .fst)
          (funext Rem (_ ↦ Q) (equiv_inverse_map Q Rem (residue_quotient_equiv n c (iso_residue n c i))) (i .fst .map)
            (r ↦ inverse_at_known_point Q Rem (residue_quotient_equiv n c (iso_residue n c i)) (i .fst .map r) r
              (concat Rem (residue_quotient_map n c (iso_residue n c i) (i .fst .map r))
                (equiv_inverse_map Rem Q (i .fst) (i .fst .map r)) r
                (residue_quotient_is_inverse n c i (i .fst .map r)) (equiv_retraction Rem Q (i .fst) r))))))
      (rho ↦ residue_equal n c (iso_residue n c (residue_iso n c rho)) rho
        (x ↦ double_inverse_map Q Rem (residue_quotient_equiv n c rho) (quotient_class X R x)))

{` Given divisibility, maps of cycles X → ℤ/m correspond to classes in X/m. `}
def class_residue (n : Nat) (c : Cycles) (divides : OrderDivides (principal_order (suc. n)) (cycle_order c))
  : ModQuotient n (c .fst .fst .fst) (c .fst .snd) → CycleResidues n c
  ≔ let X ≔ c .fst .fst .fst in let t ≔ c .fst .snd in let R ≔ mod_relation n X t in
    let Rem ≔ Remainder (suc. n) in
    quotient_rec X (CycleResidues n c) R (residues_set n c) (x0 ↦ cycle_residue n c divides x0 .fst)
      (x0 x1 o ↦ let r0 ≔ cycle_residue n c divides x0 in
        refl ((w ↦ w .fst) : PointedPermutationMaps X Rem t (modular_successor_equiv n) x1 (remainder_at n zero. star.) → CycleResidues n c)
          (pointed_cycle_maps_prop X Rem (remainder_set (suc. n)) t (modular_successor_equiv n) (c .snd) x1 (remainder_at n zero. star.)
            (r0 .fst, concat Rem (r0 .fst .fst x1) (r0 .fst .fst x0) (remainder_at n zero. star.)
              (inverse Rem (r0 .fst .fst x0) (r0 .fst .fst x1) (residue_respects n c (r0 .fst) x0 x1 o)) (r0 .snd))
            (cycle_residue n c divides x1)))

def residue_zero_class (n : Nat) (c : Cycles) (rho : CycleResidues n c) : ModQuotient n (c .fst .fst .fst) (c .fst .snd)
  ≔ equiv_inverse_map (ModQuotient n (c .fst .fst .fst) (c .fst .snd)) (Remainder (suc. n))
      (residue_quotient_equiv n c rho) (remainder_at n zero. star.)

def residues_classes_equiv (n : Nat) (c : Cycles) (divides : OrderDivides (principal_order (suc. n)) (cycle_order c))
  : Equiv (CycleResidues n c) (ModQuotient n (c .fst .fst .fst) (c .fst .snd))
  ≔ let X ≔ c .fst .fst .fst in let t ≔ c .fst .snd in let R ≔ mod_relation n X t in
    let Q ≔ ModQuotient n X t in let Rem ≔ Remainder (suc. n) in
    quasi_inverse_equiv (CycleResidues n c) Q (residue_zero_class n c) (class_residue n c divides)
      (rho ↦ let V ≔ residue_zero_class n c rho in
        mere_rec (BookFiber X Q (quotient_class X R) V) (Id (CycleResidues n c) (class_residue n c divides V) rho)
          (residues_set n c (class_residue n c divides V) rho)
          (w ↦ concat (CycleResidues n c) (class_residue n c divides V) (cycle_residue n c divides (w .fst) .fst) rho
            (refl (class_residue n c divides) (w .snd))
            (refl ((u ↦ u .fst) : PointedPermutationMaps X Rem t (modular_successor_equiv n) (w .fst) (remainder_at n zero. star.)
                → CycleResidues n c)
              (pointed_cycle_maps_prop X Rem (remainder_set (suc. n)) t (modular_successor_equiv n) (c .snd) (w .fst)
                (remainder_at n zero. star.) (cycle_residue n c divides (w .fst))
                (rho, calc
                  rho .fst (w .fst) = residue_quotient_map n c rho V
                    by refl (residue_quotient_map n c rho) (inverse Q V (quotient_class X R (w .fst)) (w .snd))
                  = remainder_at n zero. star.
                    by equiv_counit Q Rem (residue_quotient_equiv n c rho) (remainder_at n zero. star.) ∎))))
          (quotient_surjective X R V))
      (quotient_prop_induction X R (V ↦ Id Q (residue_zero_class n c (class_residue n c divides V)) V)
        (V ↦ quotient_set X R (residue_zero_class n c (class_residue n c divides V)) V)
        (x0 ↦ inverse_at_known_point Q Rem (residue_quotient_equiv n c (cycle_residue n c divides x0 .fst))
          (quotient_class X R x0) (remainder_at n zero. star.) (cycle_residue n c divides x0 .snd)))

{` The preimage of q : Cyc_e → Cyc_m at the standard m-cycle is Σ_{(X,t):Cyc_e} X/m. `}
def order_quotient_preimage_classes (n : Nat) (e : Order) (he : OrderDivides (principal_order (suc. n)) e)
  : Equiv (BookFiber (CyclesOfOrder e) (CycleComponent (suc. n)) (order_quotient_cycle n e he) (principal_component_point (suc. n)))
      (Σ (CyclesOfOrder e) (u ↦ ModQuotient n (u .fst .fst .fst .fst) (u .fst .fst .snd)))
  ≔ let D ≔ CyclesOfOrder e in
    let F0 ≔ BookFiber D (CycleComponent (suc. n)) (order_quotient_cycle n e he) (principal_component_point (suc. n)) in
    let F1 ≔ Σ D (u ↦ Id Cycles (finite_standard_cycle n) (QuotientCycle n (u .fst))) in
    let F2 ≔ Σ D (u ↦ StandardQuotientIsos n (u .fst)) in
    let F3 ≔ Σ D (u ↦ CycleResidues n (u .fst)) in
    let F4 ≔ Σ D (u ↦ ModQuotient n (u .fst .fst .fst .fst) (u .fst .fst .snd)) in
    let e1 ≔ family_equiv D (u ↦ Id (CycleComponent (suc. n)) (principal_component_point (suc. n)) (order_quotient_cycle n e he u))
      (u ↦ Id Cycles (finite_standard_cycle n) (QuotientCycle n (u .fst)))
      (u ↦ subtype_path_equiv Cycles (x ↦ Mere (Id Cycles (finite_standard_cycle n) x))
        (x ↦ mere_isprop (Id Cycles (finite_standard_cycle n) x)) (principal_component_point (suc. n)) (order_quotient_cycle n e he u)) in
    let e2 ≔ family_equiv D (u ↦ Id Cycles (finite_standard_cycle n) (QuotientCycle n (u .fst))) (u ↦ StandardQuotientIsos n (u .fst))
      (u ↦ cycle_paths_equiv (finite_standard_cycle n) (QuotientCycle n (u .fst))) in
    let e3 ≔ family_equiv D (u ↦ StandardQuotientIsos n (u .fst)) (u ↦ CycleResidues n (u .fst))
      (u ↦ standard_quotient_isos_residues n (u .fst)) in
    let e4 ≔ family_equiv D (u ↦ CycleResidues n (u .fst)) (u ↦ ModQuotient n (u .fst .fst .fst .fst) (u .fst .fst .snd))
      (u ↦ residues_classes_equiv n (u .fst) (order_component_divides n e he u)) in
    compose_equiv F0 F3 F4 (compose_equiv F0 F2 F3 (compose_equiv F0 F1 F2 e1 e2) e3) e4

{` xca:image-Cmd-to-Cm, final clause: the preimage of q : Cyc_md → Cyc_m at
   the standard m-cycle is identified with Cyc_d. `}
def root_quotient_preimage_equiv (n : Nat) (d : Order)
  : Equiv (BookFiber (CyclesOfOrder (order_root n d)) (CycleComponent (suc. n))
        (order_quotient_cycle n (order_root n d) (root_order_divides n d)) (principal_component_point (suc. n)))
      (CyclesOfOrder d)
  ≔ let W ≔ CyclesOfOrder (order_root n d) in
    let F0 ≔ BookFiber W (CycleComponent (suc. n)) (order_quotient_cycle n (order_root n d) (root_order_divides n d))
      (principal_component_point (suc. n)) in
    let F4 ≔ Σ W (u ↦ ModQuotient n (u .fst .fst .fst .fst) (u .fst .fst .snd)) in
    let F5 ≔ Σ W (u ↦ root_order_fibers n d u) in
    compose_equiv F0 F5 (CyclesOfOrder d)
      (compose_equiv F0 F4 F5 (order_quotient_preimage_classes n (order_root n d) (root_order_divides n d))
        (family_equiv W (u ↦ ModQuotient n (u .fst .fst .fst .fst) (u .fst .fst .snd)) (u ↦ root_order_fibers n d u)
          (u ↦ canonical_inverse_equiv (root_order_fibers n d u) (ModQuotient n (u .fst .fst .fst .fst) (u .fst .fst .snd))
            (root_order_fiber_equiv n d u))))
      (sum_of_fibers_equiv (CyclesOfOrder d) W (cycle_root_of_order n d))
