export "81-circle-degree-coverings"

def map_image_predicate (A B : Type) (f : A → B) : Subtypes B
  ≔ b ↦ (Mere (BookFiber A B f b), mere_isprop (BookFiber A B f b))

def map_image_homotopy (A B : Type) (f g : A → B) (h : (a : A) → Id B (f a) (g a))
  : Id (Subtypes B) (map_image_predicate A B f) (map_image_predicate A B g)
  ≔ funext B (_ ↦ PropTypes) (map_image_predicate A B f) (map_image_predicate A B g)
      (b ↦ proposition_extensionality (map_image_predicate A B f b) (map_image_predicate A B g b)
        (trunc_map native_truncation (BookFiber A B f b) (BookFiber A B g b)
          (w ↦ (w .fst, concat B b (f (w .fst)) (g (w .fst)) (w .snd) (h (w .fst)))))
        (trunc_map native_truncation (BookFiber A B g b) (BookFiber A B f b)
          (w ↦ (w .fst, concat B b (g (w .fst)) (f (w .fst)) (w .snd)
            (inverse B (f (w .fst)) (g (w .fst)) (h (w .fst)))))))

def path_to_induction (A : Type) (b : A) (P : (a : A) → Id A a b → Type)
  (base : P b (refl b)) (a : A) (p : Id A a b) : P a p
  ≔ transport (Σ A (x ↦ Id A x b)) (t ↦ P (t .fst) (t .snd))
      (b, refl b) (a, p)
      (inverse (Σ A (x ↦ Id A x b)) (a, p) (b, refl b) (path_to_contractible A b .contract (a, p))) base

def based_loop_winding (C : CircleSignature) (t : MapsInto (C .carrier)) (a : t .fst)
  (base : Id (C .carrier) (t .snd a) (C .base)) (p : Id (t .fst) a a) : Int
  ≔ circle_winding C (transport (C .carrier) (z ↦ Id (C .carrier) z z)
      (t .snd a) (C .base) base (refl (t .snd) p))

def based_loop_image (C : CircleSignature) (t : MapsInto (C .carrier)) (a : t .fst)
  (base : Id (C .carrier) (t .snd a) (C .base)) : Subtypes Int
  ≔ map_image_predicate (Id (t .fst) a a) Int (based_loop_winding C t a base)

def based_loop_winding_refl (C : CircleSignature) (t : MapsInto (C .carrier)) (a : t .fst)
  (base : Id (C .carrier) (t .snd a) (C .base))
  : Id Int (based_loop_winding C t a base (refl a)) int_zero
  ≔ concat Int (based_loop_winding C t a base (refl a)) (circle_winding C (refl (C .base))) int_zero
      (refl (circle_winding C)
        (pathover_transport_equiv (C .carrier) (z ↦ Id (C .carrier) z z)
          (t .snd a) (C .base) base (refl (t .snd a)) (refl (C .base))
          .map (apd (C .carrier) (z ↦ Id (C .carrier) z z) (z ↦ refl z) (t .snd a) (C .base) base)))
      (circle_winding_refl C)

def total_loop_winding (C : CircleSignature) (R : C .carrier → Type) (x : R (C .base))
  (p : Id (Σ (C .carrier) R) (C .base, x) (C .base, x)) : Int ≔ circle_winding C (p .fst)

def total_loop_image (C : CircleSignature) (R : C .carrier → Type) (x : R (C .base)) : Subtypes Int
  ≔ map_image_predicate (Id (Σ (C .carrier) R) (C .base, x) (C .base, x)) Int (total_loop_winding C R x)

def family_period_to_image (C : CircleSignature) (R : C .carrier → Type) (x : R (C .base)) (n : Int)
  (period : PowerPeriod (R (C .base)) (family_monodromy C R) n) : total_loop_image C R x n .fst
  ≔ let p ≔ orbit_total_path C R x x
      (n, inverse (R (C .base)) (permutation_power (R (C .base)) (family_monodromy C R) n x) x (period (refl x))) in
    mere (BookFiber (Id (Σ (C .carrier) R) (C .base, x) (C .base, x)) Int (total_loop_winding C R x) n)
      (p, inverse Int (circle_winding C (loop_power (C .carrier) (C .base) (C .loop) n)) n (circle_winding_power C n))

def family_image_to_period (C : CircleSignature) (R : C .carrier → Type) (hs : isSet (R (C .base)))
  (cyclic : Cyclic (R (C .base)) (family_monodromy C R)) (x : R (C .base)) (n : Int)
  : total_loop_image C R x n .fst → PowerPeriod (R (C .base)) (family_monodromy C R) n
  ≔ mere_rec (BookFiber (Id (Σ (C .carrier) R) (C .base, x) (C .base, x)) Int (total_loop_winding C R x) n)
      (PowerPeriod (R (C .base)) (family_monodromy C R) n) (power_period_prop (R (C .base)) hs (family_monodromy C R) n)
      (w ↦ cycle_period_from_point (R (C .base)) hs (family_monodromy C R) cyclic x n (calc
        permutation_power (R (C .base)) (family_monodromy C R) n x
        = permutation_power (R (C .base)) (family_monodromy C R) (total_loop_winding C R x (w .fst)) x
          by refl ((k ↦ permutation_power (R (C .base)) (family_monodromy C R) k x) : Int → R (C .base)) (w .snd)
        = x by total_path_orbit C R x x (w .fst) .snd ∎))

def family_periods_image (C : CircleSignature) (R : C .carrier → Type) (hs : isSet (R (C .base)))
  (cyclic : Cyclic (R (C .base)) (family_monodromy C R)) (x : R (C .base))
  : Id (Subtypes Int) (cycle_periods (R (C .base)) hs (family_monodromy C R)) (total_loop_image C R x)
  ≔ funext Int (_ ↦ PropTypes) (cycle_periods (R (C .base)) hs (family_monodromy C R)) (total_loop_image C R x)
      (n ↦ proposition_extensionality (cycle_periods (R (C .base)) hs (family_monodromy C R) n)
        (total_loop_image C R x n) (family_period_to_image C R x n) (family_image_to_period C R hs cyclic x n))

def family_based_image_at_base (C : CircleSignature) (R : C .carrier → Type) (x : R (C .base))
  : Id (Subtypes Int) (based_loop_image C (map_of_family (C .carrier) R) (C .base, x) (refl (C .base)))
      (total_loop_image C R x)
  ≔ map_image_homotopy (Id (Σ (C .carrier) R) (C .base, x) (C .base, x)) Int
      (based_loop_winding C (map_of_family (C .carrier) R) (C .base, x) (refl (C .base))) (total_loop_winding C R x)
      (p ↦ refl (circle_winding C) (transport_refl (C .carrier) (z ↦ Id (C .carrier) z z) (C .base) (p .fst)))

def family_based_periods_image (C : CircleSignature) (R : C .carrier → Type) (hs : isSet (R (C .base)))
  (cyclic : Cyclic (R (C .base)) (family_monodromy C R))
  (a : Σ (C .carrier) R) (base : Id (C .carrier) (a .fst) (C .base))
  : Id (Subtypes Int) (cycle_periods (R (C .base)) hs (family_monodromy C R))
      (based_loop_image C (map_of_family (C .carrier) R) a base)
  ≔ path_to_induction (C .carrier) (C .base)
      (z base ↦ (x : R z) → Id (Subtypes Int) (cycle_periods (R (C .base)) hs (family_monodromy C R))
        (based_loop_image C (map_of_family (C .carrier) R) (z, x) base))
      (x ↦ concat (Subtypes Int) (cycle_periods (R (C .base)) hs (family_monodromy C R))
        (total_loop_image C R x) (based_loop_image C (map_of_family (C .carrier) R) (C .base, x) (refl (C .base)))
        (family_periods_image C R hs cyclic x)
        (inverse (Subtypes Int) (based_loop_image C (map_of_family (C .carrier) R) (C .base, x) (refl (C .base)))
          (total_loop_image C R x) (family_based_image_at_base C R x)))
      (a .fst) base (a .snd)

def AllBasedLoopImages (C : CircleSignature) (H : Subtypes Int) (t : MapsInto (C .carrier)) : Type
  ≔ (a : t .fst) (base : Id (C .carrier) (t .snd a) (C .base)) → Id (Subtypes Int) H (based_loop_image C t a base)

{` The chosen comparison f(a)=base is explicit.  No path is extracted from
   connectedness; the result holds for every such comparison. `}
def covering_periods_based_image (C : CircleSignature) (c : ConnectedCoverings (C .carrier))
  : AllBasedLoopImages C (CyclePeriods (circle_connected_coverings_cycles C .map c)) (forget_covering (C .carrier) (c .fst))
  ≔ let t ≔ forget_covering (C .carrier) (c .fst) in
    let R ≔ fibers_of_map (C .carrier) t in
    let H ≔ CyclePeriods (circle_connected_coverings_cycles C .map c) in
    transport (MapsInto (C .carrier)) (AllBasedLoopImages C H)
      (map_of_family (C .carrier) R) t (maps_families_eta (C .carrier) t)
      (family_based_periods_image C R (c .fst .snd .snd (C .base)) (circle_connected_coverings_cycles C .map c .snd))
