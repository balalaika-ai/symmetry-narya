export "114-zero-image-composite-comparison"

def zero_image_triangle_path_from_reverse (A C B : Type) (g : A → C) (hg : ConnectedFibers A C g)
  (h : C → B) (hh : IsCovering C B h) (f : A → B) (q : Id (A → B) (compose A C B h g) f)
  : Id (Factorizations A B f) (zero_image_triangular_factorization A B f)
      (C, (g, (h, inverse (A → B) (compose A C B h g) f q)))
  ≔ let F ≔ compose A C B h g in
    J (A → B) F
      (f q ↦ Id (Factorizations A B f) (zero_image_triangular_factorization A B f)
        (C, (g, (h, inverse (A → B) F f q))))
      (concat (Factorizations A B F) (zero_image_triangular_factorization A B F)
        (C, (g, (h, refl F))) (C, (g, (h, inverse (A → B) F F (refl F))))
        (zero_composite_factorization_path A C B g hg h hh)
        (refl ((r ↦ (C, (g, (h, r)))) : Id (A → B) F F → Factorizations A B F)
          (inverse (Id (A → B) F F) (inverse (A → B) F F (refl F)) (refl F)
            (inverse_refl (A → B) F)))) f q

{` The specified r is retained. Path induction first gives inverse of
   inverse r, then the inverse law identifies that path with r itself. `}
def zero_image_triangular_contraction (A C B : Type) (g : A → C) (hg : ConnectedFibers A C g)
  (h : C → B) (hh : IsCovering C B h) (f : A → B) (r : Id (A → B) f (compose A C B h g))
  : Id (Factorizations A B f) (zero_image_triangular_factorization A B f) (C, (g, (h, r)))
  ≔ let F ≔ compose A C B h g in
    concat (Factorizations A B f) (zero_image_triangular_factorization A B f)
      (C, (g, (h, inverse (A → B) F f (inverse (A → B) f F r)))) (C, (g, (h, r)))
      (zero_image_triangle_path_from_reverse A C B g hg h hh f (inverse (A → B) f F r))
      (refl ((s ↦ (C, (g, (h, s)))) : Id (A → B) f F → Factorizations A B f)
        (inverse_inverse (A → B) f F r))

def zero_factorization_properties_prop (A B : Type) (f : A → B) (t : Factorizations A B f)
  : isProp (ZeroFactorizationProperties A B f t)
  ≔ product_prop (ZeroConnectedMap A (t .fst) (t .snd .fst)) (IsCovering (t .fst) B (t .snd .snd .fst))
      (zero_connected_map_prop A (t .fst) (t .snd .fst))
      (covering_property_prop B (t .fst, t .snd .snd .fst))

def zero_image_factorization_contraction (A B : Type) (f : A → B) (u : ZeroImageFactorizations A B f)
  : Id (ZeroImageFactorizations A B f) (zero_image_factorization A B f) u
  ≔ equivalence_injective (ZeroImageFactorizations A B f)
      (Σ (Factorizations A B f) (ZeroFactorizationProperties A B f)) (zero_factorization_regroup A B f)
      (zero_image_factorization A B f) u
      (subtype_equal (Factorizations A B f) (ZeroFactorizationProperties A B f) (zero_factorization_properties_prop A B f)
        (zero_factorization_regroup A B f .map (zero_image_factorization A B f)) (zero_factorization_regroup A B f .map u)
        (zero_image_triangular_contraction A (u .fst) B (u .snd .fst)
          (zero_connected_map_fibers A (u .fst) (u .snd .fst) (u .snd .snd .snd .snd .fst))
          (u .snd .snd .fst) (u .snd .snd .snd .snd .snd) f (u .snd .snd .snd .fst)))

{` thm:n-im-univ-prop, n=0: the complete six-component type is
   contractible, with the canonical 0-image factorization as center.
   A and B are arbitrary; no circle or classical parameter is assumed. `}
def zero_image_universal_property (A B : Type) (f : A → B) : BookIsContr (ZeroImageFactorizations A B f)
  ≔ (zero_image_factorization A B f, zero_image_factorization_contraction A B f)

def zero_image_book_universal_property (A B : Type) (f : A → B)
  : BookIsContr (Σ (Factorizations A B f) (ZeroFactorizationProperties A B f))
  ≔ book_contractibility_equiv (ZeroImageFactorizations A B f)
      (Σ (Factorizations A B f) (ZeroFactorizationProperties A B f)) (zero_factorization_regroup A B f) .map
      (zero_image_universal_property A B f)
