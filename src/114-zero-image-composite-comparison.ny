export "113-factorization-comparisons"

def function_loop_from_points (A B : Type) (f : A → B) (q : Id (A → B) f f)
  (hq : (a : A) → Id (Id B (f a) (f a)) (q (refl a)) (refl (f a)))
  : Id (Id (A → B) f f) q (refl f)
  ≔ equivalence_injective (Id (A → B) f f) (Homotopy A (_ ↦ B) f f)
      (function_extensionality A (_ ↦ B) f f) q (refl f)
      (funext A (a ↦ Id B (f a) (f a)) (happly A (_ ↦ B) f f q) (happly A (_ ↦ B) f f (refl f)) hq)

def zero_composite_section (A X B : Type) (g : A → X) (hg : ConnectedFibers A X g)
  (h : X → B) (hh : IsCovering X B h) (z : ZeroImage A B (compose A X B h g))
  : BookFiber X B h (z .fst)
  ≔ composite_truncated_fiber_equiv A X B g hg h hh (z .fst) .map (z .snd)

def zero_composite_lift (A X B : Type) (g : A → X) (hg : ConnectedFibers A X g)
  (h : X → B) (hh : IsCovering X B h) : ZeroImage A B (compose A X B h g) → X
  ≔ z ↦ zero_composite_section A X B g hg h hh z .fst

def zero_composite_carrier_equiv (A X B : Type) (g : A → X) (hg : ConnectedFibers A X g)
  (h : X → B) (hh : IsCovering X B h) : Equiv (ZeroImage A B (compose A X B h g)) X
  ≔ (zero_composite_lift A X B g hg h hh,
      compose_equiv (ZeroImage A B (compose A X B h g)) (Σ B (BookFiber X B h)) X
        (family_equiv B (b ↦ SetTrunc (BookFiber A B (compose A X B h g) b)) (BookFiber X B h)
          (composite_truncated_fiber_equiv A X B g hg h hh)) (sum_of_fibers_equiv X B h) .equiv)

def zero_composite_right_triangle (A X B : Type) (g : A → X) (hg : ConnectedFibers A X g)
  (h : X → B) (hh : IsCovering X B h)
  : Id (ZeroImage A B (compose A X B h g) → B) (zero_image_include A B (compose A X B h g))
      (compose (ZeroImage A B (compose A X B h g)) X B h (zero_composite_lift A X B g hg h hh))
  ≔ funext (ZeroImage A B (compose A X B h g)) (_ ↦ B) (zero_image_include A B (compose A X B h g))
      (compose (ZeroImage A B (compose A X B h g)) X B h (zero_composite_lift A X B g hg h hh))
      (z ↦ zero_composite_section A X B g hg h hh z .snd)

def zero_composite_right_triangle_restriction (A X B : Type) (g : A → X) (hg : ConnectedFibers A X g)
  (h : X → B) (hh : IsCovering X B h)
  : Id (Id (A → B) (compose A X B h g) (compose A X B h g))
      (refl (precompose A (ZeroImage A B (compose A X B h g)) B (zero_image_factor A B (compose A X B h g)))
        (zero_composite_right_triangle A X B g hg h hh)) (refl (compose A X B h g))
  ≔ function_loop_from_points A B (compose A X B h g)
      (refl (precompose A (ZeroImage A B (compose A X B h g)) B (zero_image_factor A B (compose A X B h g)))
        (zero_composite_right_triangle A X B g hg h hh))
      (a ↦ inverse (Id B (h (g a)) (h (g a))) (refl (h (g a)))
        (zero_composite_right_triangle A X B g hg h hh (refl (zero_image_factor A B (compose A X B h g) a)))
        (funext_beta (ZeroImage A B (compose A X B h g)) (_ ↦ B)
          (zero_image_include A B (compose A X B h g))
          (compose (ZeroImage A B (compose A X B h g)) X B h (zero_composite_lift A X B g hg h hh))
          (z ↦ zero_composite_section A X B g hg h hh z .snd) (zero_image_factor A B (compose A X B h g) a)))

def zero_composite_comparison_coherence (A X B : Type) (g : A → X) (hg : ConnectedFibers A X g)
  (h : X → B) (hh : IsCovering X B h)
  : Id (RightDiagonals A X B h (compose A X B h g)) (g, refl (compose A X B h g))
      (factorization_compare_map A (ZeroImage A B (compose A X B h g)) X B (compose A X B h g)
        (zero_image_factor A B (compose A X B h g)) (zero_image_include A B (compose A X B h g))
        (zero_image_triangle A B (compose A X B h g)) h
        (zero_composite_lift A X B g hg h hh, zero_composite_right_triangle A X B g hg h hh))
  ≔ let f ≔ compose A X B h g in
    let q ≔ refl (precompose A (ZeroImage A B f) B (zero_image_factor A B f))
      (zero_composite_right_triangle A X B g hg h hh) in
    (refl g, inverse (Id (A → B) f f) (concat (A → B) f f f (refl f) q) (refl f)
      (concat (Id (A → B) f f) (concat (A → B) f f f (refl f) q) q (refl f)
        (concat_1p (A → B) f f q) (zero_composite_right_triangle_restriction A X B g hg h hh)))

def zero_image_triangular_factorization (A B : Type) (f : A → B) : Factorizations A B f
  ≔ (ZeroImage A B f, (zero_image_factor A B f, (zero_image_include A B f, zero_image_triangle A B f)))

def zero_composite_factorization_path (A X B : Type) (g : A → X) (hg : ConnectedFibers A X g)
  (h : X → B) (hh : IsCovering X B h)
  : Id (Factorizations A B (compose A X B h g))
      (zero_image_triangular_factorization A B (compose A X B h g))
      (X, (g, (h, refl (compose A X B h g))))
  ≔ factorization_equivalence_comparison A (ZeroImage A B (compose A X B h g)) X B (compose A X B h g)
      (zero_image_factor A B (compose A X B h g)) (zero_image_include A B (compose A X B h g))
      (zero_image_triangle A B (compose A X B h g)) g h (refl (compose A X B h g))
      (zero_composite_carrier_equiv A X B g hg h hh) (zero_composite_right_triangle A X B g hg h hh)
      (zero_composite_comparison_coherence A X B g hg h hh)
