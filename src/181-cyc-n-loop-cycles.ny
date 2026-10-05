export "180-cyc-n-loops"

def cyc_path_fst_concat (b : Nat) (x y z : CycleComponent (suc. b))
  (p : Id (CycleComponent (suc. b)) x y) (q : Id (CycleComponent (suc. b)) y z)
  : Id (Id Cycles (x .fst) (z .fst)) (concat (CycleComponent (suc. b)) x y z p q .fst)
      (concat Cycles (x .fst) (y .fst) (z .fst) (p .fst) (q .fst))
  ≔ map_path_concat (CycleComponent (suc. b)) Cycles (u ↦ u .fst) x y z p q

def standard_loop_predecessor (b : Nat) (p : Id Cycles (finite_standard_cycle b) (finite_standard_cycle b))
  (x : Remainder (suc. b))
  : Id (Remainder (suc. b)) (cycle_path_evaluate (finite_standard_cycle b) (finite_standard_cycle b) p (modular_predecessor b x))
      (modular_predecessor b (cycle_path_evaluate (finite_standard_cycle b) (finite_standard_cycle b) p x))
  ≔ let c ≔ finite_standard_cycle b in
    let h ≔ cycle_path_evaluate c c p in
    calc
      h (modular_predecessor b x) = modular_predecessor b (modular_successor b (h (modular_predecessor b x)))
        by inverse (Remainder (suc. b)) (modular_predecessor b (modular_successor b (h (modular_predecessor b x))))
          (h (modular_predecessor b x)) (modular_predecessor_successor b (h (modular_predecessor b x)))
      = modular_predecessor b (h (modular_successor b (modular_predecessor b x)))
        by refl (modular_predecessor b) (inverse (Remainder (suc. b)) (h (modular_successor b (modular_predecessor b x)))
          (modular_successor b (h (modular_predecessor b x))) (cycle_paths_equiv c c .map p .snd (modular_predecessor b x)))
      = modular_predecessor b (h x)
        by refl ((y ↦ modular_predecessor b (h y)) : Remainder (suc. b) → Remainder (suc. b)) (modular_successor_predecessor b x) ∎

{` Evaluation of loops at 0 turns composition with sigma_n on either side
   into the predecessor. `}
def cyc_loop_left (b : Nat)
  (t : Id (CycleComponent (suc. b)) (principal_component_point (suc. b)) (principal_component_point (suc. b)))
  : Id (Remainder (suc. b))
      (cyc_loop_equiv b .map (concat (CycleComponent (suc. b)) (principal_component_point (suc. b))
        (principal_component_point (suc. b)) (principal_component_point (suc. b)) (cyc_generator b) t))
      (modular_predecessor b (cyc_loop_equiv b .map t))
  ≔ let c ≔ finite_standard_cycle b in let C ≔ CycleComponent (suc. b) in let pt ≔ principal_component_point (suc. b) in
    let r0 : Remainder (suc. b) ≔ remainder_at b zero. star. in
    let ev ≔ ((p ↦ cycle_path_evaluate c c p r0) : Id Cycles c c → Remainder (suc. b)) in
    calc
      ev (concat C pt pt pt (cyc_generator b) t .fst) = ev (concat Cycles c c c (cyc_generator b .fst) (t .fst))
        by refl ev (cyc_path_fst_concat b pt pt pt (cyc_generator b) t)
      = cycle_path_evaluate c c (t .fst) (cycle_path_evaluate c c (cyc_generator b .fst) r0)
        by cycle_path_evaluation_concat c c c (cyc_generator b .fst) (t .fst) r0
      = cycle_path_evaluate c c (t .fst) (cycle_path_evaluate c c (standard_predecessor_loop b) r0)
        by refl ((p ↦ cycle_path_evaluate c c (t .fst) (cycle_path_evaluate c c p r0)) : Id Cycles c c → Remainder (suc. b))
          (cyc_generator_underlying b)
      = cycle_path_evaluate c c (t .fst) (modular_predecessor b r0)
        by refl (cycle_path_evaluate c c (t .fst)) (standard_predecessor_loop_action b r0)
      = modular_predecessor b (ev (t .fst)) by standard_loop_predecessor b (t .fst) r0 ∎

def cyc_loop_right (b : Nat)
  (t : Id (CycleComponent (suc. b)) (principal_component_point (suc. b)) (principal_component_point (suc. b)))
  : Id (Remainder (suc. b))
      (cyc_loop_equiv b .map (concat (CycleComponent (suc. b)) (principal_component_point (suc. b))
        (principal_component_point (suc. b)) (principal_component_point (suc. b)) t (cyc_generator b)))
      (modular_predecessor b (cyc_loop_equiv b .map t))
  ≔ let c ≔ finite_standard_cycle b in let C ≔ CycleComponent (suc. b) in let pt ≔ principal_component_point (suc. b) in
    let r0 : Remainder (suc. b) ≔ remainder_at b zero. star. in
    let ev ≔ ((p ↦ cycle_path_evaluate c c p r0) : Id Cycles c c → Remainder (suc. b)) in
    calc
      ev (concat C pt pt pt t (cyc_generator b) .fst) = ev (concat Cycles c c c (t .fst) (cyc_generator b .fst))
        by refl ev (cyc_path_fst_concat b pt pt pt t (cyc_generator b))
      = cycle_path_evaluate c c (cyc_generator b .fst) (ev (t .fst))
        by cycle_path_evaluation_concat c c c (t .fst) (cyc_generator b .fst) r0
      = cycle_path_evaluate c c (standard_predecessor_loop b) (ev (t .fst))
        by refl ((p ↦ cycle_path_evaluate c c p (ev (t .fst))) : Id Cycles c c → Remainder (suc. b)) (cyc_generator_underlying b)
      = modular_predecessor b (ev (t .fst)) by standard_predecessor_loop_action b (ev (t .fst)) ∎

def cyc_loop_refl (b : Nat)
  : Id (Remainder (suc. b)) (cyc_loop_equiv b .map (refl (principal_component_point (suc. b)))) (remainder_at b zero. star.)
  ≔ cycle_automorphisms_identity_beta (finite_standard_cycle b) (remainder_at b zero. star.)

def cyc_loop_power (b : Nat) (k : Nat)
  : Id (Remainder (suc. b))
      (cyc_loop_equiv b .map (loop_power_nat (CycleComponent (suc. b)) (principal_component_point (suc. b)) (cyc_generator b) k))
      (iterate (Remainder (suc. b)) (modular_predecessor b) k (cyc_loop_equiv b .map (refl (principal_component_point (suc. b)))))
  ≔ match k [
  | zero. ↦ refl (cyc_loop_equiv b .map (refl (principal_component_point (suc. b))))
  | suc. k ↦ concat (Remainder (suc. b))
      (cyc_loop_equiv b .map (loop_power_nat (CycleComponent (suc. b)) (principal_component_point (suc. b)) (cyc_generator b) (suc. k)))
      (modular_predecessor b (cyc_loop_equiv b .map (loop_power_nat (CycleComponent (suc. b)) (principal_component_point (suc. b)) (cyc_generator b) k)))
      (iterate (Remainder (suc. b)) (modular_predecessor b) (suc. k) (cyc_loop_equiv b .map (refl (principal_component_point (suc. b)))))
      (cyc_loop_right b (loop_power_nat (CycleComponent (suc. b)) (principal_component_point (suc. b)) (cyc_generator b) k))
      (refl (modular_predecessor b) (cyc_loop_power b k)) ]

def modular_predecessor_period (b : Nat) (r : Remainder (suc. b))
  : Id (Remainder (suc. b)) (iterate (Remainder (suc. b)) (modular_predecessor b) (suc. b) r) r
  ≔ calc
      iterate (Remainder (suc. b)) (modular_predecessor b) (suc. b) r
      = iterate (Remainder (suc. b)) (modular_predecessor b) (suc. b) (iterate (Remainder (suc. b)) (modular_successor b) (suc. b) r)
        by refl (iterate (Remainder (suc. b)) (modular_predecessor b) (suc. b))
          (inverse (Remainder (suc. b)) (iterate (Remainder (suc. b)) (modular_successor b) (suc. b) r) r
            (happly (Remainder (suc. b)) (_ ↦ Remainder (suc. b))
              (permutation_power (Remainder (suc. b)) (modular_successor_equiv b) (pos. (suc. b)))
              (identity (Remainder (suc. b))) (finite_standard_period b) r))
      = r by iterate_cancel (Remainder (suc. b)) (modular_successor b) (modular_predecessor b)
        (modular_predecessor_successor b) (suc. b) r ∎

{` The equation refl = sigma_n^n in pt_n = pt_n. `}
def cyc_generator_order (b : Nat)
  : Id (Id (CycleComponent (suc. b)) (principal_component_point (suc. b)) (principal_component_point (suc. b)))
      (refl (principal_component_point (suc. b)))
      (loop_power_nat (CycleComponent (suc. b)) (principal_component_point (suc. b)) (cyc_generator b) (suc. b))
  ≔ let L ≔ Id (CycleComponent (suc. b)) (principal_component_point (suc. b)) (principal_component_point (suc. b)) in
    let r ≔ cyc_loop_equiv b .map (refl (principal_component_point (suc. b))) in
    equivalence_injective L (Remainder (suc. b)) (cyc_loop_equiv b) (refl (principal_component_point (suc. b)))
      (loop_power_nat (CycleComponent (suc. b)) (principal_component_point (suc. b)) (cyc_generator b) (suc. b))
      (inverse (Remainder (suc. b))
        (cyc_loop_equiv b .map (loop_power_nat (CycleComponent (suc. b)) (principal_component_point (suc. b)) (cyc_generator b) (suc. b)))
        r
        (concat (Remainder (suc. b))
          (cyc_loop_equiv b .map (loop_power_nat (CycleComponent (suc. b)) (principal_component_point (suc. b)) (cyc_generator b) (suc. b)))
          (iterate (Remainder (suc. b)) (modular_predecessor b) (suc. b) r) r
          (cyc_loop_power b (suc. b)) (modular_predecessor_period b r)))

def cyc_loops_set (b : Nat)
  : isSet (Id (CycleComponent (suc. b)) (principal_component_point (suc. b)) (principal_component_point (suc. b)))
  ≔ let L ≔ Id (CycleComponent (suc. b)) (principal_component_point (suc. b)) (principal_component_point (suc. b)) in
    hlevel_two_to_set L (hlevel_equiv (suc. (suc. zero.)) (Remainder (suc. b)) L
      (canonical_inverse_equiv L (Remainder (suc. b)) (cyc_loop_equiv b))
      (set_to_hlevel_two (Remainder (suc. b)) (remainder_set (suc. b))))

{` The loops of pt_n with composition by sigma_n form a cycle. `}
def cyc_loops_cyclic (b : Nat)
  : Cyclic (Id (CycleComponent (suc. b)) (principal_component_point (suc. b)) (principal_component_point (suc. b)))
      (loop_concat_equiv (CycleComponent (suc. b)) (principal_component_point (suc. b)) (principal_component_point (suc. b))
        (cyc_generator b))
  ≔ let C ≔ CycleComponent (suc. b) in let pt ≔ principal_component_point (suc. b) in
    let L ≔ Id C pt pt in let E ≔ cyc_loop_equiv b in
    let Einv ≔ equiv_inverse_map L (Remainder (suc. b)) E in
    cyclic_transfer (Remainder (suc. b)) L (modular_predecessor_equiv b) (loop_concat_equiv C pt pt (cyc_generator b))
      (canonical_inverse_equiv L (Remainder (suc. b)) E)
      (r ↦ inverse_at_known_point L (Remainder (suc. b)) E (concat C pt pt pt (cyc_generator b) (Einv r)) (modular_predecessor b r)
        (concat (Remainder (suc. b)) (E .map (concat C pt pt pt (cyc_generator b) (Einv r)))
          (modular_predecessor b (E .map (Einv r))) (modular_predecessor b r)
          (cyc_loop_left b (Einv r)) (refl (modular_predecessor b) (equiv_counit L (Remainder (suc. b)) E r))))
      (modular_predecessor_cyclic b)

{` If refl a = s^n, every period of sigma_n-composition on loops of pt_n
   is a period of s-composition on a = b. `}
def cyc_loops_period_inclusion (b : Nat) (A : Type) (a y : A) (s : Id A a a) (hB : isSet (Id A a y))
  (h : Id (Id A a a) (refl a) (loop_power_nat A a s (suc. b)))
  : PeriodInclusion (Id (CycleComponent (suc. b)) (principal_component_point (suc. b)) (principal_component_point (suc. b)))
      (Id A a y)
      (loop_concat_equiv (CycleComponent (suc. b)) (principal_component_point (suc. b)) (principal_component_point (suc. b))
        (cyc_generator b))
      (loop_concat_equiv A a y s)
  ≔ let C ≔ CycleComponent (suc. b) in let pt ≔ principal_component_point (suc. b) in
    let L ≔ Id C pt pt in let E ≔ cyc_loop_equiv b in let R ≔ Remainder (suc. b) in
    let e ≔ loop_concat_equiv C pt pt (cyc_generator b) in let f ≔ loop_concat_equiv A a y s in
    let r ≔ E .map (refl pt) in
    z P ↦
    let fixed ≔ calc
        permutation_power R (modular_predecessor_equiv b) z r = E .map (permutation_power L e z (refl pt))
          by inverse R (E .map (permutation_power L e z (refl pt))) (permutation_power R (modular_predecessor_equiv b) z r)
            (permutation_power_intertwine L R e (modular_predecessor_equiv b) (E .map) (cyc_loop_left b) z (refl pt))
        = r by refl (E .map) (happly L (_ ↦ L) (permutation_power L e z) (identity L) P (refl pt)) ∎ in
    let per_pred ≔ cycle_period_from_point R (remainder_set (suc. b)) (modular_predecessor_equiv b)
      (modular_predecessor_cyclic b) r z fixed in
    let per_succ : PowerPeriod R (modular_successor_equiv b) (int_neg z)
      ≔ funext R (_ ↦ R) (permutation_power R (modular_successor_equiv b) (int_neg z)) (identity R) (x ↦
        concat R (permutation_power R (modular_successor_equiv b) (int_neg z) x)
          (permutation_power R (modular_predecessor_equiv b) z x) x
          (inverse R (permutation_power R (modular_predecessor_equiv b) z x)
            (permutation_power R (modular_successor_equiv b) (int_neg z) x)
            (permutation_power_left_inverse R (modular_successor_equiv b) (modular_predecessor_equiv b)
              (modular_predecessor_successor b) z x))
          (happly R (_ ↦ R) (permutation_power R (modular_predecessor_equiv b) z) (identity R) per_pred x)) in
    let mult : Multiples (suc. b) z .fst
      ≔ trunc_map native_truncation (MultipleWitness (suc. b) (int_neg z)) (MultipleWitness (suc. b) z)
        (w ↦ (int_neg (w .fst), calc
          z = int_neg (int_neg z) by inverse Int (int_neg (int_neg z)) z (int_neg_neg z)
          = int_neg (int_mul (w .fst) (pos. (suc. b))) by refl int_neg (w .snd)
          = int_mul (int_neg (w .fst)) (pos. (suc. b))
            by inverse Int (int_mul (int_neg (w .fst)) (pos. (suc. b))) (int_neg (int_mul (w .fst) (pos. (suc. b))))
              (int_mul_neg_left_pos (w .fst) (suc. b)) ∎))
        (standard_period_multiple b (int_neg z) per_succ) in
    let fn : PowerPeriod (Id A a y) f (pos. (suc. b))
      ≔ funext (Id A a y) (_ ↦ Id A a y) (permutation_power (Id A a y) f (pos. (suc. b))) (identity (Id A a y)) (q ↦ calc
        iterate (Id A a y) (t ↦ concat A a a y s t) (suc. b) q = concat A a a y (loop_power_nat A a s (suc. b)) q
          by iterate_loop_concat A a y s (suc. b) q
        = concat A a a y (refl a) q
          by refl ((l ↦ concat A a a y l q) : Id A a a → Id A a y)
            (inverse (Id A a a) (refl a) (loop_power_nat A a s (suc. b)) h)
        = q by concat_1p A a y q ∎) in
    multiple_subgroup_member (cycle_periods (Id A a y) hB f) (permutation_period_laws (Id A a y) hB f) (suc. b) fn z mult
