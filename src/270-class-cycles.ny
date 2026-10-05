export "224-constructed-circle-checks"
export "244-k-cycle-count"
export "232-n-image-universal-property"
export "211-exponential-fibers"

{` Evaluation of a cycle path followed by its inverse. `}
def cycle_path_evaluate_inverse (a b : Cycles) (p : Id Cycles a b) (x : a .fst .fst .fst)
  : Id (a .fst .fst .fst) (cycle_path_evaluate b a (inverse Cycles a b p) (cycle_path_evaluate a b p x)) x
  ≔ J Cycles a
      (b p ↦ (x : a .fst .fst .fst)
        → Id (a .fst .fst .fst) (cycle_path_evaluate b a (inverse Cycles a b p) (cycle_path_evaluate a b p x)) x)
      (x ↦ concat (a .fst .fst .fst)
        (cycle_path_evaluate a a (inverse Cycles a a (refl a)) (cycle_path_evaluate a a (refl a) x))
        (cycle_path_evaluate a a (refl a) (cycle_path_evaluate a a (refl a) x)) x
        (refl ((q ↦ cycle_path_evaluate a a q (cycle_path_evaluate a a (refl a) x)) : Id Cycles a a → a .fst .fst .fst)
          (inverse_refl Cycles a))
        (concat (a .fst .fst .fst) (cycle_path_evaluate a a (refl a) (cycle_path_evaluate a a (refl a) x))
          (cycle_path_evaluate a a (refl a) x) x
          (transport_refl Type (Y ↦ Y) (a .fst .fst .fst) (cycle_path_evaluate a a (refl a) x))
          (transport_refl Type (Y ↦ Y) (a .fst .fst .fst) x)))
      b p x

{` Evaluation of the path of cycles determined by an isomorphism. `}
def iso_path_evaluate (c d : Cycles) (i : PermutationIsomorphisms (c .fst) (d .fst)) (x : c .fst .fst .fst)
  : Id (d .fst .fst .fst)
      (cycle_path_evaluate c d
        (equiv_inverse_map (Id Cycles c d) (PermutationIsomorphisms (c .fst) (d .fst)) (cycle_paths_equiv c d) i) x)
      (i .fst .map x)
  ≔ refl ((j ↦ j .fst .map x) : PermutationIsomorphisms (c .fst) (d .fst) → d .fst .fst .fst)
      (equiv_counit (Id Cycles c d) (PermutationIsomorphisms (c .fst) (d .fst)) (cycle_paths_equiv c d) i)

{` Restriction of an equivalence to a subset preserved in both directions. `}
def subset_restrict_equiv (X : Type) (S : X → Type) (hS : (x : X) → isProp (S x)) (e : Equiv X X)
  (fw : (x : X) → S x → S (e .map x)) (bw : (x : X) → S x → S (equiv_inverse_map X X e x))
  : Equiv (Σ X S) (Σ X S)
  ≔ quasi_inverse_equiv (Σ X S) (Σ X S)
      (w ↦ (e .map (w .fst), fw (w .fst) (w .snd)))
      (w ↦ (equiv_inverse_map X X e (w .fst), bw (w .fst) (w .snd)))
      (w ↦ subtype_equal X S hS
        (equiv_inverse_map X X e (e .map (w .fst)), bw (e .map (w .fst)) (fw (w .fst) (w .snd))) w
        (equiv_retraction X X e (w .fst)))
      (w ↦ subtype_equal X S hS
        (e .map (equiv_inverse_map X X e (w .fst)), fw (equiv_inverse_map X X e (w .fst)) (bw (w .fst) (w .snd))) w
        (equiv_counit X X e (w .fst)))

{` A class V of X/m is preserved by t^m and its inverse. `}
def class_step_forward (n : Nat) (X : Type) (t : Equiv X X) (V : ModQuotient n X t) (x : X) (h : V .fst x .fst)
  : V .fst (mod_power n X t .map x) .fst
  ≔ quotient_class_property X (mod_relation n X t) V (mod_power n X t .map x) .map
      (concat (ModQuotient n X t) V (quotient_class X (mod_relation n X t) x)
        (quotient_class X (mod_relation n X t) (mod_power n X t .map x))
        (equiv_inverse_map (Id (ModQuotient n X t) V (quotient_class X (mod_relation n X t) x)) (V .fst x .fst)
          (quotient_class_property X (mod_relation n X t) V x) h)
        (equiv_inverse_map (Id (ModQuotient n X t) (quotient_class X (mod_relation n X t) x)
            (quotient_class X (mod_relation n X t) (mod_power n X t .map x)))
          (Rel X (mod_relation n X t) x (mod_power n X t .map x))
          (quotient_effective X (mod_relation n X t) x (mod_power n X t .map x))
          (mere (OrbitWitness X (mod_power n X t) x (mod_power n X t .map x))
            (pos. (suc. zero.), refl (mod_power n X t .map x)))))

def class_step_backward (n : Nat) (X : Type) (t : Equiv X X) (V : ModQuotient n X t) (x : X) (h : V .fst x .fst)
  : V .fst (equiv_inverse_map X X (mod_power n X t) x) .fst
  ≔ let y ≔ equiv_inverse_map X X (mod_power n X t) x in
    quotient_class_property X (mod_relation n X t) V y .map
      (concat (ModQuotient n X t) V (quotient_class X (mod_relation n X t) x)
        (quotient_class X (mod_relation n X t) y)
        (equiv_inverse_map (Id (ModQuotient n X t) V (quotient_class X (mod_relation n X t) x)) (V .fst x .fst)
          (quotient_class_property X (mod_relation n X t) V x) h)
        (equiv_inverse_map (Id (ModQuotient n X t) (quotient_class X (mod_relation n X t) x)
            (quotient_class X (mod_relation n X t) y))
          (Rel X (mod_relation n X t) x y)
          (quotient_effective X (mod_relation n X t) x y)
          (mere (OrbitWitness X (mod_power n X t) x y) (neg. zero., refl y))))

{` The class V as a set with the restriction of t^m. `}
def ClassCarrier (n : Nat) (c : Cycles) (V : ModQuotient n (c .fst .fst .fst) (c .fst .snd)) : Type
  ≔ Σ (c .fst .fst .fst) (x ↦ V .fst x .fst)

def class_carrier_set (n : Nat) (c : Cycles) (V : ModQuotient n (c .fst .fst .fst) (c .fst .snd))
  : isSet (ClassCarrier n c V)
  ≔ sigma_set (c .fst .fst .fst) (x ↦ V .fst x .fst) (c .fst .fst .snd)
      (x ↦ prop_is_set (V .fst x .fst) (V .fst x .snd))

def class_permutation (n : Nat) (c : Cycles) (V : ModQuotient n (c .fst .fst .fst) (c .fst .snd))
  : Equiv (ClassCarrier n c V) (ClassCarrier n c V)
  ≔ subset_restrict_equiv (c .fst .fst .fst) (x ↦ V .fst x .fst) (x ↦ V .fst x .snd)
      (mod_power n (c .fst .fst .fst) (c .fst .snd))
      (class_step_forward n (c .fst .fst .fst) (c .fst .snd) V)
      (class_step_backward n (c .fst .fst .fst) (c .fst .snd) V)

def class_power_first (n : Nat) (c : Cycles) (V : ModQuotient n (c .fst .fst .fst) (c .fst .snd))
  (z : Int) (w : ClassCarrier n c V)
  : Id (c .fst .fst .fst) (permutation_power (ClassCarrier n c V) (class_permutation n c V) z w .fst)
      (permutation_power (c .fst .fst .fst) (mod_power n (c .fst .fst .fst) (c .fst .snd)) z (w .fst))
  ≔ permutation_power_intertwine (ClassCarrier n c V) (c .fst .fst .fst) (class_permutation n c V)
      (mod_power n (c .fst .fst .fst) (c .fst .snd)) (v ↦ v .fst)
      (v ↦ refl (mod_power n (c .fst .fst .fst) (c .fst .snd) .map (v .fst))) z w

def class_cyclic (n : Nat) (c : Cycles) (V : ModQuotient n (c .fst .fst .fst) (c .fst .snd))
  : Cyclic (ClassCarrier n c V) (class_permutation n c V)
  ≔ let X ≔ c .fst .fst .fst in let t ≔ c .fst .snd in
    let R ≔ mod_relation n X t in let Q ≔ ModQuotient n X t in let M ≔ mod_power n X t in
    let C ≔ ClassCarrier n c V in let P ≔ class_permutation n c V in
    let S ≔ ((x ↦ V .fst x .fst) : X → Type) in
    let back ≔ ((x ↦ equiv_inverse_map (Id Q V (quotient_class X R x)) (V .fst x .fst) (quotient_class_property X R V x))
      : (x : X) → V .fst x .fst → Id Q V (quotient_class X R x)) in
    (mere_rec (BookFiber X Q (quotient_class X R) V) (Mere C) (mere_isprop C)
       (a ↦ mere C (a .fst, quotient_class_property X R V (a .fst) .map (a .snd)))
       (quotient_surjective X R V),
     w w' ↦ mere_rec (OrbitWitness X M (w .fst) (w' .fst)) (SameOrbit C P w w') (same_orbit_prop C P w w')
       (o ↦ mere (OrbitWitness C P w w') (o .fst,
          subtype_equal X S (x ↦ V .fst x .snd) w' (permutation_power C P (o .fst) w)
            (concat X (w' .fst) (permutation_power X M (o .fst) (w .fst)) (permutation_power C P (o .fst) w .fst)
              (o .snd)
              (inverse X (permutation_power C P (o .fst) w .fst) (permutation_power X M (o .fst) (w .fst))
                (class_power_first n c V (o .fst) w)))))
       (quotient_effective X R (w .fst) (w' .fst) .map
         (concat Q (quotient_class X R (w .fst)) V (quotient_class X R (w' .fst))
           (inverse Q V (quotient_class X R (w .fst)) (back (w .fst) (w .snd)))
           (back (w' .fst) (w' .snd)))))

def class_cycle (n : Nat) (c : Cycles) (V : ModQuotient n (c .fst .fst .fst) (c .fst .snd)) : Cycles
  ≔ (((ClassCarrier n c V, class_carrier_set n c V), class_permutation n c V), class_cyclic n c V)

{` For an infinite cycle, (V, t^m) is again an infinite cycle. `}
def class_cycle_periods (n : Nat) (y : CycleComponent zero.) (V : ModQuotient n (y .fst .fst .fst .fst) (y .fst .fst .snd))
  : Id (Subtypes Int) (CyclePeriods (class_cycle n (y .fst) V)) ZeroPeriods
  ≔ let c ≔ y .fst in let X ≔ c .fst .fst .fst in let t ≔ c .fst .snd in
    let M ≔ mod_power n X t in
    let C ≔ ClassCarrier n c V in let P ≔ class_permutation n c V in
    inclusion_antisym Int (CyclePeriods (class_cycle n c V)) ZeroPeriods
      (z hz ↦ mere_rec C (Id Int z int_zero) (int_set z int_zero)
        (w0 ↦
          let fixed ≔ calc
            permutation_power X t (int_mul (pos. (suc. n)) z) (w0 .fst) = permutation_power X M z (w0 .fst)
              by permutation_power_scaled X t (suc. n) z (w0 .fst)
            = permutation_power C P z w0 .fst
              by inverse X (permutation_power C P z w0 .fst) (permutation_power X M z (w0 .fst)) (class_power_first n c V z w0)
            = w0 .fst by refl ((w ↦ w .fst) : C → X) (happly C (_ ↦ C) (permutation_power C P z) (identity C) hz w0) ∎ in
          let period ≔ cycle_period_from_point X (c .fst .fst .snd) t (c .snd) (w0 .fst) (int_mul (pos. (suc. n)) z) fixed in
          let product_zero ≔ infinite_period_is_zero (int_mul (pos. (suc. n)) z)
            (transport (Subtypes Int) (H ↦ H (int_mul (pos. (suc. n)) z) .fst) (CyclePeriods c) (CyclePeriods infinite_cycle)
              (inverse (Subtypes Int) (CyclePeriods infinite_cycle) (CyclePeriods c)
                (cycle_paths_imply_periods infinite_cycle c (y .snd))) period) in
          int_mul_cancel_pos n z int_zero (calc
            int_mul z (pos. (suc. n)) = int_mul (pos. (suc. n)) z by int_mul_comm z (pos. (suc. n))
            = int_zero by product_zero
            = int_mul int_zero (pos. (suc. n))
              by inverse Int (int_mul int_zero (pos. (suc. n))) int_zero (int_mul_zero_left_pos (suc. n)) ∎))
        (class_cyclic n c V .fst))
      (z p ↦ zero_is_period (class_cycle n c V) z p)

def class_cycle_infinite (n : Nat) (y : CycleComponent zero.) (V : ModQuotient n (y .fst .fst .fst .fst) (y .fst .fst .snd))
  : Mere (Id Cycles infinite_cycle (class_cycle n (y .fst) V))
  ≔ cycle_periods_imply_paths infinite_cycle (class_cycle n (y .fst) V)
      (concat (Subtypes Int) (CyclePeriods infinite_cycle) ZeroPeriods (CyclePeriods (class_cycle n (y .fst) V))
        infinite_cycle_periods
        (inverse (Subtypes Int) (CyclePeriods (class_cycle n (y .fst) V)) ZeroPeriods (class_cycle_periods n y V)))
