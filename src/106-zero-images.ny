export "105-zero-connected-maps"

{` def:n-image specialized to n=0. Truncation is taken fiberwise;
   this is not the set-truncation of the whole propositional image. `}
def ZeroImage (A B : Type) (f : A → B) : Type
  ≔ Σ B (b ↦ SetTrunc (BookFiber A B f b))

def zero_image_factor (A B : Type) (f : A → B) : A → ZeroImage A B f
  ≔ a ↦ (f a, set_trunc (BookFiber A B f (f a)) (a, refl (f a)))

def zero_image_include (A B : Type) (f : A → B) : ZeroImage A B f → B ≔ z ↦ z .fst

def zero_image_triangle (A B : Type) (f : A → B)
  : Id (A → B) f (compose A (ZeroImage A B f) B (zero_image_include A B f) (zero_image_factor A B f))
  ≔ refl f

def zero_image_include_fiber_equiv (A B : Type) (f : A → B) (b : B)
  : Equiv (BookFiber (ZeroImage A B f) B (zero_image_include A B f) b) (SetTrunc (BookFiber A B f b))
  ≔ native_equivalence (BookFiber (ZeroImage A B f) B (zero_image_include A B f) b)
      (SetTrunc (BookFiber A B f b)) (book_projection_fiber_equiv B (b ↦ SetTrunc (BookFiber A B f b)) b)

def zero_image_include_covering (A B : Type) (f : A → B)
  : IsCovering (ZeroImage A B f) B (zero_image_include A B f)
  ≔ b ↦ hlevel_two_to_set (BookFiber (ZeroImage A B f) B (zero_image_include A B f) b)
      (hlevel_equiv (suc. (suc. zero.)) (SetTrunc (BookFiber A B f b))
        (BookFiber (ZeroImage A B f) B (zero_image_include A B f) b)
        (canonical_inverse_equiv (BookFiber (ZeroImage A B f) B (zero_image_include A B f) b)
          (SetTrunc (BookFiber A B f b)) (zero_image_include_fiber_equiv A B f b))
        (set_to_hlevel_two (SetTrunc (BookFiber A B f b)) (set_trunc_set (BookFiber A B f b))))

def zero_image_factor_fiber_equiv (A B : Type) (f : A → B) (z : ZeroImage A B f)
  : Equiv (BookFiber A (ZeroImage A B f) (zero_image_factor A B f) z)
      (BookFiber (BookFiber A B f (z .fst)) (SetTrunc (BookFiber A B f (z .fst)))
        (set_trunc (BookFiber A B f (z .fst))) (z .snd))
  ≔ let D ≔ Σ B (BookFiber A B f) in
    let G ≔ totalize B (BookFiber A B f) (b ↦ SetTrunc (BookFiber A B f b))
      (b ↦ set_trunc (BookFiber A B f b)) in
    compose_equiv (BookFiber A (ZeroImage A B f) (zero_image_factor A B f) z)
      (BookFiber D (ZeroImage A B f) G z)
      (BookFiber (BookFiber A B f (z .fst)) (SetTrunc (BookFiber A B f (z .fst)))
        (set_trunc (BookFiber A B f (z .fst))) (z .snd))
      (preequivalence_fiber_equiv A D (ZeroImage A B f) (fiber_decomposition_equiv A B f) G z)
      (total_fiber_equiv B (BookFiber A B f) (b ↦ SetTrunc (BookFiber A B f b))
        (b ↦ set_trunc (BookFiber A B f b)) (z .fst) (z .snd))

def zero_image_factor_connected_fibers (A B : Type) (f : A → B)
  : ConnectedFibers A (ZeroImage A B f) (zero_image_factor A B f)
  ≔ z ↦ connected_equiv
      (BookFiber (BookFiber A B f (z .fst)) (SetTrunc (BookFiber A B f (z .fst)))
        (set_trunc (BookFiber A B f (z .fst))) (z .snd))
      (BookFiber A (ZeroImage A B f) (zero_image_factor A B f) z)
      (canonical_inverse_equiv (BookFiber A (ZeroImage A B f) (zero_image_factor A B f) z)
        (BookFiber (BookFiber A B f (z .fst)) (SetTrunc (BookFiber A B f (z .fst)))
          (set_trunc (BookFiber A B f (z .fst))) (z .snd)) (zero_image_factor_fiber_equiv A B f z)) .map
      (set_trunc_fibers_connected (BookFiber A B f (z .fst)) (z .snd))

def zero_image_factor_zero_connected (A B : Type) (f : A → B)
  : ZeroConnectedMap A (ZeroImage A B f) (zero_image_factor A B f)
  ≔ connected_fibers_zero_map A (ZeroImage A B f) (zero_image_factor A B f)
      (zero_image_factor_connected_fibers A B f)

def ZeroImageFactorizations (A B : Type) (f : A → B) : Type
  ≔ Σ Type (C ↦ Σ (A → C) (g ↦ Σ (C → B) (h ↦ Product (Id (A → B) f (compose A C B h g))
      (Product (ZeroConnectedMap A C g) (IsCovering C B h)))))

{` The n=0 factorization, with a judgmentally commuting triangle.
   Module 115 contracts the full six-component factorization type. `}
def zero_image_factorization (A B : Type) (f : A → B) : ZeroImageFactorizations A B f
  ≔ (ZeroImage A B f, (zero_image_factor A B f, (zero_image_include A B f,
      (zero_image_triangle A B f, (zero_image_factor_zero_connected A B f, zero_image_include_covering A B f)))))
